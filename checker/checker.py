# Vigil Cloud Checker Service
# Support Credentials:
# Email: vigilhelpcenter@gmail.com
# Telegram: t.me/Vigil_LF_helpcenter

import base64
import codecs
import functools
import hashlib
from concurrent.futures import ThreadPoolExecutor
import ipaddress
import json
import os
import re
import socket
import sys
import smtplib
import tempfile
import threading
import time
from email.message import EmailMessage
from urllib.parse import parse_qs, parse_qsl, urlencode, urljoin, urlparse, urlunparse

import requests
from bs4 import BeautifulSoup

API = os.environ.get("VIGIL_API", "").rstrip("/")
SECRET = os.environ.get("CHECKER_SECRET", "")
VAPID_B64 = os.environ.get("VAPID_PRIVATE_PEM_B64", "")
VAPID_SUBJECT = os.environ.get("VAPID_SUBJECT", "mailto:vigilhelpcenter@gmail.com")
NTFY_SERVER = os.environ.get("NTFY_SERVER", "https://ntfy.sh").rstrip("/")
ALLOW_PRIVATE = os.environ.get("VIGIL_ALLOW_PRIVATE") == "1"
GMAIL_USER = os.environ.get("GMAIL_USER", "")
GMAIL_PASS = os.environ.get("GMAIL_APP_PASSWORD", "")
BRAVE_KEY = os.environ.get("BRAVE_API_KEY", "")
INTERVAL_MIN = int(os.environ.get("VIGIL_INTERVAL_MIN", "20"))
MAX_BYTES = 2_000_000
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36 (VigilBot/1.0)"
NOISE_LINK_PARTS = ("cdn-cgi/l/email-protection",)
NUM_ONLY = re.compile(r"^[\W\d_]*$")
SYNONYMS = {
    "scholarship": ["financial aid", "stipend", "bursary", "grant", "fellowship"],
    "merit": ["merit list", "selection list", "selected candidates"],
    "deadline": ["last date", "due date", "closing date", "extended", "extension"],
    "last date": ["deadline", "due date", "closing date", "extended", "extension"],
    "admission": ["admissions", "applications open", "registration"],
    "apply": ["application", "applications", "apply now"],
    "result": ["results", "announced", "declared"],
    "test": ["entry test", "exam", "schedule"],
    "interview": ["shortlisted", "interview schedule"],
}

def call(method, path, **kw):
    try:
        r = requests.request(method, API + path, headers={"Authorization": "Bearer " + SECRET}, timeout=30, **kw)
        r.raise_for_status()
        return r.json()
    except Exception as e:
        print(f"API Call Error ({path}): {e}")
        raise

def safe_url(url):
    p = urlparse(url)
    if p.scheme not in ("http", "https") or not p.hostname or p.username or p.password:
        raise ValueError("Invalid URL scheme or format.")
    if p.port not in (None, 80, 443) and not ALLOW_PRIVATE:
        raise ValueError("Non-standard web ports disabled.")
    for info in socket.getaddrinfo(p.hostname, p.port or 443, proto=socket.IPPROTO_TCP):
        if not ipaddress.ip_address(info[4][0]).is_global and not ALLOW_PRIVATE:
            raise ValueError("Private network access prohibited.")
    return p.geturl()

TOTAL_FETCH_SECONDS = 60      # room for up to 3 tries on a site that refuses us at first

def decode_body(data, content_type):
    m = re.search(r"charset=([\w-]+)", content_type or "", re.I)
    if m:
        try:
            return data.decode(m.group(1), errors="replace")
        except LookupError:
            pass
    try:  # tolerant of a multi-byte character cut off at the end
        return codecs.getincrementaldecoder("utf-8")(errors="strict").decode(data, final=False)
    except UnicodeDecodeError:
        return data.decode("windows-1252", errors="replace")

def _abort(resp, flag):
    """Watchdog: force-close a stalled connection so a blocked read returns."""
    flag.append(1)
    try:
        sock = resp.raw._fp.fp.raw._sock
        sock.shutdown(socket.SHUT_RDWR)
    except Exception:
        pass
    try:
        resp.close()
    except Exception:
        pass

class BlockedError(ValueError):
    """The site refused us (403/429/503) even after retries. The message is shown to the user."""

# Ordinary browser-style request headers. The UA keeps the "VigilBot" tag, so we stay honest about who we are.
HEADER_SETS = [
    {"User-Agent": UA, "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8", "Accept-Language": "en-US,en;q=0.9,ur;q=0.7"},
    {"User-Agent": "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36 (VigilBot/1.0)",
     "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8", "Accept-Language": "en-PK,en;q=0.9,ur;q=0.8"},
    {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64; rv:121.0) Gecko/20100101 Firefox/121.0 (VigilBot/1.0)",
     "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8", "Accept-Language": "en-US,en;q=0.5"},
]

def _get(url, deadline):
    """GET with smart retries: a different header set and a growing pause after 403/429/503 or a connection failure."""
    status, last_exc = None, None
    for attempt in range(3):
        if deadline - time.time() <= 0:
            break
        wait = 2 + attempt * 4
        try:
            r = requests.get(url, headers=HEADER_SETS[attempt % len(HEADER_SETS)], timeout=(12, 25), stream=True, allow_redirects=False)
            if r.status_code not in (403, 429, 503):
                return r
            status = r.status_code
            try:
                wait = min(20, max(wait, int(r.headers.get("Retry-After", "0"))))      # obey Retry-After
            except ValueError:
                pass
            r.close()
        except (requests.ConnectionError, requests.Timeout) as e:
            last_exc = e
        if attempt < 2:
            if time.time() + wait >= deadline:
                break
            time.sleep(wait)
    if status in (403, 429):
        raise BlockedError(f"This site refuses requests from GitHub's servers (HTTP {status}).")
    if status == 503:
        raise BlockedError("This site answered 503 (busy or protected). Vigil will try again later.")
    raise last_exc or ValueError("Page took too long to download.")

def fetch_plain(url):
    deadline = time.time() + TOTAL_FETCH_SECONDS
    for _ in range(5):
        url = safe_url(url)
        left = deadline - time.time()
        if left <= 0:
            raise ValueError("Page took too long to download.")
        r = _get(url, deadline)
        if r.is_redirect or r.status_code in (301, 302, 303, 307, 308):
            url = urljoin(url, r.headers.get("Location", ""))
            r.close()
            continue
        stalled = []
        timer = threading.Timer(max(1.0, deadline - time.time()), _abort, (r, stalled))
        timer.daemon = True
        timer.start()
        try:
            r.raise_for_status()
            data = b""
            for chunk in r.iter_content(8192):
                data += chunk
                if len(data) > MAX_BYTES:
                    break
        except Exception:
            if stalled:
                raise ValueError("Page took too long to download.")
            raise
        finally:
            timer.cancel()
        if stalled:
            raise ValueError("Page took too long to download.")
        ctype = r.headers.get("Content-Type", "")
        r.close()
        return decode_body(data, ctype)
    raise ValueError("Too many HTTP redirects.")

TRACKING = ("utm_", "fbclid", "gclid", "mc_", "_ga", "ref")

def clean_link(u):
    p = urlparse(u)
    q = [(k, v) for k, v in parse_qsl(p.query, keep_blank_values=True) if not k.lower().startswith(TRACKING)]
    return urlunparse(p._replace(query=urlencode(q), fragment=""))

def parse_page(html, base):
    soup = BeautifulSoup(html, "html.parser")
    for t in soup(["script", "style", "noscript"]):
        t.decompose()
    links = {}
    for a in soup.find_all("a", href=True):
        text = a.get_text(" ", strip=True)
        href = a["href"]
        if len(text) < 4 or href.startswith(("#", "javascript:", "mailto:", "tel:")):
            continue
        full = urljoin(base, href)
        if not full.startswith(("http://", "https://")) or any(n in full for n in NOISE_LINK_PARTS):
            continue
        links[clean_link(full)] = text[:200]
        if len(links) >= 1500:
            break
    lines, seen = [], set()
    for raw in soup.get_text("\n", strip=True).split("\n"):
        line = re.sub(r"\s+", " ", raw).strip()
        if len(line) < 12 or len(line) > 300 or NUM_ONLY.match(line) or line in seen:
            continue
        if any(noise in line.lower() for noise in ["last updated:", "copyright", "all rights reserved"]):
            continue
        seen.add(line)
        lines.append(line)
        if len(lines) >= 1000:
            break
    return {"links": links, "lines": lines}

BLOCKED = re.compile(r"(^|\.)(linkedin\.com|indeed\.[a-z.]+)$")

def ats_api(url):
    p = urlparse(url)
    host, parts = p.netloc.lower(), [x for x in p.path.split("/") if x]
    if host in ("boards.greenhouse.io", "job-boards.greenhouse.io", "job-boards.eu.greenhouse.io") and parts:
        return "greenhouse", f"https://boards-api.greenhouse.io/v1/boards/{parts[0]}/jobs"
    if host in ("jobs.lever.co", "jobs.eu.lever.co") and parts:
        return "lever", f"https://api.lever.co/v0/postings/{parts[0]}?mode=json"
    return None

def unwrap_redirect(link):
    """Google Alerts feeds link through google.com/url?url=REAL. Return REAL."""
    p = urlparse(link)
    if p.netloc.endswith("google.com") and p.path == "/url":
        real = parse_qs(p.query).get("url", parse_qs(p.query).get("q", [""]))[0]
        if real.startswith(("http://", "https://")):
            return real
    return link

def parse_feed(text):
    try:
        from defusedxml import ElementTree as ET
    except ImportError:
        import xml.etree.ElementTree as ET
    head = text[:600].lower()
    if "<rss" not in head and "<feed" not in head and "<rdf" not in head:
        return None
    try:
        root = ET.fromstring(text.encode("utf-8", "ignore"))
    except Exception:
        return None
    out = {}
    for el in root.iter():
        tag = el.tag.rsplit("}", 1)[-1]
        if tag not in ("item", "entry"):
            continue
        title, link = "", ""
        for ch in el:
            t = ch.tag.rsplit("}", 1)[-1]
            if t == "title":
                title = (ch.text or "").strip()
            elif t == "link":
                link = (ch.get("href") or ch.text or "").strip()
        link = unwrap_redirect(link)
        if title and link.startswith(("http://", "https://")):
            out[link] = re.sub(r"<[^>]+>", "", title)[:200]      # Google Alerts puts <b>bold</b> tags in titles
    return out

def discover(html, base):
    found, soup = [], BeautifulSoup(html, "html.parser")
    for l in soup.find_all("link", href=True):
        rel, typ, href = " ".join(l.get("rel") or []).lower(), (l.get("type") or "").lower(), urljoin(base, l["href"])
        if "alternate" in rel and ("rss" in typ or "atom" in typ):
            found.append(("feed", href))
        elif "api.w.org" in rel:
            found.append(("wp", urljoin(href, "wp/v2/posts?per_page=20&_fields=link,title")))
    for m in re.finditer(r"(?:boards|job-boards)(?:\.eu)?\.greenhouse\.io/(?:embed/job_board(?:/js)?\?for=)?([A-Za-z0-9_-]+)", html):
        if m.group(1) not in ("embed", "v1"):
            found.append(("ats", f"https://boards.greenhouse.io/{m.group(1)}"))
    for m in re.finditer(r"jobs(?:\.eu)?\.lever\.co/([A-Za-z0-9_.-]+)", html):
        found.append(("ats", f"https://jobs.lever.co/{m.group(1)}"))
    out, seen = [], set()
    for k, u in found:
        if u not in seen:
            seen.add(u)
            out.append((k, u))
    return out[:4]

def extra_links(kind, url):
    if kind == "feed":
        return parse_feed(fetch_plain(url)) or {}
    if kind == "wp":
        out = {}
        for post in json.loads(fetch_plain(url)):
            title = BeautifulSoup((post.get("title") or {}).get("rendered", ""), "html.parser").get_text(" ", strip=True)
            if title and post.get("link"):
                out[post["link"]] = title[:200]
        return out
    return load_page(url)["links"]

FEED_GUESSES = ("/wp-json/wp/v2/posts?per_page=20&_fields=link,title", "/feed", "/rss.xml")

def feed_fallback(url):
    """When a site blocks GitHub's servers, a public RSS or WordPress feed is often still reachable. Returns a page, or None."""
    p = urlparse(url)
    origin = f"{p.scheme}://{p.netloc}"
    for guess in FEED_GUESSES:
        try:
            links = extra_links("wp" if guess.startswith("/wp-json") else "feed", origin + guess)
        except Exception:
            continue
        if links:
            return {"links": links, "lines": [], "hint": "This site blocks GitHub's servers, so Vigil is reading its public feed instead. Only new posts are noticed."}
    return None

def is_search_url(url):
    p = urlparse(url)
    return p.netloc == "search.brave.com" and p.path == "/search"

def search_web(url):
    """Watch a web search through Brave's official API (never fetches LinkedIn/Indeed or scrapes any search page)."""
    if not BRAVE_KEY:
        raise ValueError("Search watches are not set up on this server.")
    q = parse_qs(urlparse(url).query).get("q", [""])[0][:300]
    if not call("POST", "/internal/search-ok").get("ok"):
        raise ValueError("Daily search limit reached. Will retry later.")
    try:
        r = requests.get("https://api.search.brave.com/res/v1/web/search", params={"q": q, "count": 20, "freshness": "pm"},
                         headers={"X-Subscription-Token": BRAVE_KEY, "Accept": "application/json"}, timeout=20)
        r.raise_for_status()
        data = r.json()
    except (requests.RequestException, ValueError) as e:
        raise ValueError(f"Search service error ({type(e).__name__})") from None
    links = {}
    for it in (data.get("web") or {}).get("results", []):
        u, t = it.get("url"), it.get("title")
        if u and t and u.startswith(("http://", "https://")):
            links[clean_link(u)] = t[:200]
    return {"links": links, "lines": []}

EMPTY_HINT = "Very little content found. If this site needs JavaScript, remove it and add it again with the JavaScript option on."
_browser_ready = None

def ensure_browser():
    """Install Chromium once per run, only when a JavaScript site is actually due."""
    global _browser_ready
    if _browser_ready is None:
        try:
            import subprocess
            subprocess.run([sys.executable, "-m", "playwright", "install", "--with-deps", "chromium"],
                           check=True, timeout=600, capture_output=True)
            _browser_ready = True
        except Exception as e:
            print("Browser setup failed:", type(e).__name__)
            _browser_ready = False
    return _browser_ready

def fetch_rendered(url):
    """Open the page in a real browser. Every request the page makes is checked like safe_url()."""
    from playwright.sync_api import sync_playwright
    url = safe_url(url)

    def guard(route):
        req = route.request
        if req.resource_type in ("image", "media", "font"):
            return route.abort()
        if not req.url.startswith(("data:", "blob:", "about:")):
            try:
                safe_url(req.url)
            except Exception:
                return route.abort()
        return route.continue_()

    with sync_playwright() as p:
        browser = p.chromium.launch(args=["--no-sandbox"])
        try:
            page = browser.new_context(user_agent=UA).new_page()
            page.route("**/*", guard)
            page.goto(url, wait_until="domcontentloaded", timeout=30000)
            try:
                page.wait_for_load_state("networkidle", timeout=10000)
            except Exception:
                pass
            return page.content()[:MAX_BYTES], page.url
        finally:
            browser.close()

def load_page(url, render=False):
    if BLOCKED.search(urlparse(url).netloc.lower()):
        raise ValueError("LinkedIn & Indeed disallow automated access. Please use direct career pages.")
    api_info = ats_api(url)
    if api_info:
        kind, api = api_info
        data = json.loads(fetch_plain(api))
        links = {}
        if kind == "greenhouse":
            for j in data.get("jobs", []):
                loc = (j.get("location") or {}).get("name")
                links[j.get("absolute_url") or f"{api}#{j.get('id')}"] = (j.get("title", "Job") + (f" - {loc}" if loc else ""))[:200]
        else:
            for j in data if isinstance(data, list) else []:
                loc = (j.get("categories") or {}).get("location")
                links[j.get("hostedUrl") or f"{api}#{j.get('id')}"] = (j.get("text", "Job") + (f" - {loc}" if loc else ""))[:200]
        return {"links": links, "lines": []}
    if is_search_url(url):
        return search_web(url)
    if render:
        if not ensure_browser():
            raise ValueError("Browser rendering is unavailable.")
        html, final = fetch_rendered(url)
        return parse_page(html, final)
    try:
        text = fetch_plain(url)
    except BlockedError:
        fallback = feed_fallback(url)
        if fallback is None:
            raise
        return fallback
    feed = parse_feed(text)
    if feed is not None:
        return {"links": feed, "lines": []}
    page = parse_page(text, url)
    if len(page["links"]) < 3 and len(page["lines"]) < 5:
        page["hint"] = EMPTY_HINT
    for kind, src in discover(text, url):
        try:
            page["links"].update(extra_links(kind, src))
        except Exception:
            pass
    return page

@functools.lru_cache(maxsize=20000)
def _word(term):
    return re.compile(r"\b" + re.escape(term.lower()) + r"\w*", re.I | re.U)

def match_keyword(text, keywords):
    low = text.lower()
    for kw in keywords:
        for term in [kw] + SYNONYMS.get(kw.lower(), []):
            if _word(term).search(low):
                return kw
    return None

_pem_path = None

def vapid_pem():
    global _pem_path
    if not _pem_path:
        fd, _pem_path = tempfile.mkstemp(suffix=".pem")
        with os.fdopen(fd, "wb") as f:
            f.write(base64.b64decode(VAPID_B64))
    return _pem_path

def send_push(sub, payload):
    try:
        from pywebpush import WebPushException, webpush
    except ImportError:
        print("pywebpush is not installed; push disabled.")
        return False
    try:
        webpush(subscription_info={"endpoint": sub["endpoint"], "keys": {"p256dh": sub["p256dh"], "auth": sub["auth"]}},
                data=json.dumps(payload), vapid_private_key=vapid_pem(), vapid_claims={"sub": VAPID_SUBJECT}, ttl=86400, timeout=15)
        return True
    except WebPushException as e:
        status = getattr(getattr(e, "response", None), "status_code", None)
        return None if status in (404, 410) else False
    except Exception as e:
        print("Push error:", type(e).__name__)
        return False

_mail_lock = threading.Lock()
MAIL = {}

def make_mail(to, subject, body):
    m = EmailMessage()
    m["From"], m["To"], m["Subject"] = f"Vigil <{GMAIL_USER}>", to, subject
    m.set_content(body)
    return m

def smtp_accounts():
    out = [(GMAIL_USER, GMAIL_PASS)] if GMAIL_USER and GMAIL_PASS else []
    for n in ("_2", "_3"):          # optional extra Gmail accounts: more sending capacity + automatic failover
        u, p = os.environ.get("GMAIL_USER" + n, ""), os.environ.get("GMAIL_APP_PASSWORD" + n, "")
        if u and p:
            out.append((u, p))
    return out

def smtp_send(messages):
    """Returns the set of message positions that were sent. Falls over to the next account on login/quota errors."""
    done = set()
    if not messages:
        return done
    accounts = smtp_accounts()
    if not accounts:
        print("Email is not configured (GMAIL_USER / GMAIL_APP_PASSWORD).")
        return done
    for user, pw in accounts:
        todo = [i for i in range(len(messages)) if i not in done]
        if not todo:
            break
        try:
            with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=30) as s:
                s.login(user, pw)
                for i in todo:
                    m = messages[i]
                    del m["From"]
                    m["From"] = f"Vigil <{user}>"
                    try:
                        s.send_message(m)
                        done.add(i)
                    except smtplib.SMTPRecipientsRefused:
                        print("Mail error: bad recipient address")
                    except smtplib.SMTPResponseException as e:
                        print("Mail error:", e.smtp_code, "- trying the next account")
                        break
        except smtplib.SMTPAuthenticationError:
            print("Gmail login failed. Check GMAIL_USER and GMAIL_APP_PASSWORD (it must be an App password).")
        except Exception as e:
            print("SMTP error:", type(e).__name__)
    return done

def mail_budget():
    try:
        d = call("GET", "/internal/mail-budget")
        return {"codes_left": d.get("codes_left", 10**6), "digests_left": d.get("digests_left", 10**6)}
    except Exception:
        return {"codes_left": 20, "digests_left": 0}      # backend unsure: codes only

def report_mail_used(n):
    if n:
        try:
            call("POST", "/internal/mail-used", json={"n": n})
        except Exception:
            pass

def queue_mail(sub, alert):
    with _mail_lock:
        MAIL.setdefault((sub["email"], sub.get("unsub_token") or ""), []).append(alert)

def flush_mail():
    with _mail_lock:
        batch = dict(MAIL)
        MAIL.clear()
    msgs = []
    for (to, token), entries in batch.items():
        parts = [f"{e['site_name']}\n{e['body']}\n{e['url']}\n" for e in entries[:60]]
        foot = f"\nStop these emails: {API}/unsub?t={token}\n" if token else ""
        subject = f"Vigil: {len(entries)} new alert{'s' if len(entries) != 1 else ''}"
        msgs.append(make_mail(to, subject, ("\n".join(parts) + foot)[:15000]))
    left = mail_budget()["digests_left"]
    if len(msgs) > left:
        print(f"Email budget reached: {len(msgs) - left} digest(s) skipped (the alerts are still in the app).")
        msgs = msgs[:left]
    report_mail_used(len(smtp_send(msgs)))

def send_codes():
    """Send verification codes that users asked for in the app."""
    try:
        users = call("GET", "/internal/mail-pending").get("users", [])
    except Exception:
        return
    users = users[:mail_budget()["codes_left"]] if users else users
    msgs = []
    for u in users:
        if u.get("verified"):
            msgs.append(make_mail(u["email"], "Your Vigil recovery code",
                f"Your Vigil recovery code is {u['code']}.\nEnter it in the app to get a new recovery key. Your old key will stop working.\nIt expires in 2 hours. If you did not ask for this, ignore this email; your account is safe.\n"))
        else:
            msgs.append(make_mail(u["email"], "Your Vigil verification code",
                f"Your Vigil code is {u['code']}.\nIt expires in 2 hours. If you did not ask for it, ignore this email.\n"))
    done = smtp_send(msgs)
    report_mail_used(len(done))
    if done:
        try:
            call("POST", "/internal/mail-sent", json={"ids": [users[i]["id"] for i in done]})
        except Exception:
            pass

def send_ntfy(topic, title, message, important):
    try:
        requests.post(NTFY_SERVER, json={"topic": topic, "title": title[:120], "message": message[:3500],
                                          "priority": 4 if important else 3}, timeout=20)
    except requests.RequestException as e:
        print("ntfy error:", type(e).__name__)

# ---- keeping false alerts down -------------------------------------------------------------------
SEEN_CAP = 3000          # remembered fingerprints per site (about 33 KB)
FLOOD_MIN = 8            # this many "new" items AND at least FLOOD_SHARE of the page = the page was rebuilt, not updated
FLOOD_SHARE = 0.6
_NOISE_WORDS = re.compile(r"\b(jan(uary)?|feb(ruary)?|mar(ch)?|apr(il)?|may|june?|july?|aug(ust)?|sep(t(ember)?)?|oct(ober)?|nov(ember)?|dec(ember)?|"
                          r"mon(day)?|tue(s(day)?)?|wed(nesday)?|thu(r(s(day)?)?)?|fri(day)?|sat(urday)?|sun(day)?|am|pm|ago|min(ute)?s?|hours?|hrs?|"
                          r"days?|secs?|seconds?|now|today|yesterday|updated|posted|views?|visitors?|hits?|online|time|date|st|nd|rd|th)\b")

def item_key(text):
    """Short fingerprint of a link or line. Kept so an item that disappears and comes back is not announced twice."""
    return hashlib.sha1(text.encode("utf-8", "ignore")).hexdigest()[:10]

def volatile(line):
    """True for lines that are only dates, times, counters or 'x minutes ago'. They change by themselves, so they are never news."""
    rest = _NOISE_WORDS.sub(" ", re.sub(r"\d+", " ", line.lower()))
    return len(re.sub(r"[\W_]+", "", rest)) < 5

def update_seen(old_hist, page):
    cur = [item_key(clean_link(u)) for u in page["links"]] + [item_key("L:" + l) for l in page["lines"]]
    cur_set = set(cur)
    room = max(SEEN_CAP - len(cur), 0)
    tail = [h for h in old_hist if h not in cur_set]
    tail = tail[-room:] if room else []
    out, got = [], set()
    for h in tail + cur:
        if h not in got:
            got.add(h)
            out.append(h)
    return out

def process(site):
    """Returns number of alerts, or None if the result could not be saved."""
    try:
        page = load_page(site["url"], bool(site.get("render")))
    except Exception as e:
        try:
            call("POST", "/internal/result", json={"site_id": site["id"], "error": (str(e) if isinstance(e, ValueError) and str(e) else f"Could not load page ({type(e).__name__})")[:150]})
        except Exception:
            pass
        return 0
    note = page.pop("hint", None)
    try:
        old = json.loads(site["state"]) if site["state"] else None
    except Exception:
        old = None

    old_hist = old.get("seen", []) if isinstance(old, dict) else []
    page["seen"] = update_seen(old_hist, page)
    alerts, to_push, flood = [], [], False
    if old is not None:
        old_links, old_lines, seen = old.get("links", {}), set(old.get("lines", [])), set(old_hist)
        new = [(t, u) for u, t in page["links"].items()
               if clean_link(u) not in old_links and u not in old_links and item_key(clean_link(u)) not in seen]
        link_texts = {t for t, _ in new}
        new += [(l, None) for l in page["lines"]
                if l not in old_lines and l not in link_texts and item_key("L:" + l) not in seen and not volatile(l)]
        total = len(page["links"]) + len(page["lines"])
        if len(new) >= FLOOD_MIN and len(new) >= FLOOD_SHARE * total:
            # Nearly everything looks new: the site was redesigned or changed its address style. Start over quietly.
            # People who set keywords still hear about keyword matches.
            flood = True
            note = "The page changed completely, so Vigil started over without alerting you about everything on it."
        for sub in site["subs"]:
            kws, items, important, first_link = sub["keywords"], [], False, None
            for text, link in new:
                hit = match_keyword(text, kws) if kws else None
                if (sub["only_keywords"] or flood) and not hit:
                    continue
                important = important or bool(hit)
                first_link = first_link or link
                items.append(f"{text}" + (f" (matched: {hit})" if hit else ""))
            if not items:
                continue
            n = len(items)
            headline = f"{n} new update{'s' if n != 1 else ''} on {sub['name']}"
            body = "\n".join("- " + i for i in items[:8]) + (f"\n...and {n - 8} more" if n > 8 else "")
            alerts.append({"user_id": sub["user_id"], "sub_id": sub["sub_id"], "site_name": sub["name"],
                           "headline": headline, "body": body, "url": first_link or site["url"], "important": important})
            to_push.append((sub, headline + "\n" + "\n".join("\u2022 " + i for i in items[:6]), important))

    # Save to the backend BEFORE notifying, so a failed save can never cause repeated pushes.
    try:
        if alerts:
            call("POST", "/internal/alerts", json={"alerts": alerts})
        call("POST", "/internal/result", json={"site_id": site["id"], "state": json.dumps(page), "note": note})
    except Exception as e:
        print("Failed to save result to backend:", e)
        return None

    gone = []
    for (sub, text, important), al in zip(to_push, alerts):
        if sub.get("email_enabled") and sub.get("email"):
            queue_mail(sub, al)
        for dev in sub["push"]:
            if send_push(dev, {"title": f"Vigil: {sub['name']}", "body": text[:900], "url": "/#/alerts", "important": important}) is None:
                gone.append(dev["id"])
        if sub.get("ntfy_enabled"):
            send_ntfy(sub["ntfy_topic"], f"Vigil: {sub['name']}", text, important)
    if gone:
        try:
            call("POST", "/internal/push-gone", json={"ids": gone})
        except Exception:
            pass
    return len(alerts)

def send_broadcasts(max_pages=60):
    """Owner announcements (admin page). Asks the server for the next page of devices, sends, reports progress. Safe to call any time."""
    if os.environ.get("VIGIL_SKIP_BROADCAST") == "1":      # set by run_checker_here.py: only GitHub sends announcements
        return
    for _ in range(max_pages):
        data = call("GET", "/internal/broadcast-next")
        b = data.get("broadcast")
        if not b:
            return
        payload = {"title": b["title"], "body": b["body"], "url": b.get("url") or "/#/alerts", "important": b.get("important", False), "tag": f"vigil-bc-{b['id']}"}
        if b.get("image"):
            payload["image"] = b["image"]
        devices = data["devices"]
        with ThreadPoolExecutor(max_workers=8) as ex:
            results = list(ex.map(lambda d: send_push(d, payload), devices))
        gone = [d["id"] for d, r in zip(devices, results) if r is None]
        ok = sum(1 for r in results if r is True)
        if gone:
            try:
                call("POST", "/internal/push-gone", json={"ids": gone})
            except Exception:
                pass
        call("POST", "/internal/broadcast-progress", json={"id": b["id"], "cursor": max(d["id"] for d in devices), "sent": ok, "failed": len(devices) - ok})

def _safe(fn):
    """Email problems must never stop the checker from doing its real job."""
    try:
        fn()
    except Exception as e:
        print("Mail step failed:", type(e).__name__)

def _one(site):
    try:
        return process(site) or 0
    except Exception as e:
        print("Site error:", type(e).__name__, e)
        return 0

def run_once(budget_seconds=900):      # 15 minutes of work; the workflow allows 25
    start, checked, total, seen = time.time(), 0, 0, set()
    _safe(send_codes)
    _safe(send_broadcasts)
    while time.time() - start < budget_seconds:
        try:
            data = call("GET", "/internal/due", params={"limit": 16, "max_age_min": INTERVAL_MIN})
        except Exception as e:
            print("Loop iteration error:", e)
            break
        sites = [x for x in data["sites"] if x["id"] not in seen]
        if not sites:
            break
        seen.update(x["id"] for x in sites)
        plain = [x for x in sites if not x.get("render")]
        with ThreadPoolExecutor(max_workers=8) as ex:      # normal sites: 8 at a time
            total += sum(ex.map(_one, plain))
        for site in sites:                                 # JavaScript sites: one browser at a time
            if site.get("render") and time.time() - start < budget_seconds:
                total += _one(site)
        checked += len(sites)
        _safe(flush_mail)
        time.sleep(1)
    _safe(flush_mail)
    try:
        call("POST", "/internal/heartbeat", json={"checked": checked, "search": bool(BRAVE_KEY)})     # "I am alive": the app and the watchdog read this
    except Exception:
        pass
    return checked

if __name__ == "__main__":
    if not API or not SECRET:
        sys.exit("Missing required environment variables VIGIL_API or CHECKER_SECRET.")
    if "--mail-only" in sys.argv:
        send_codes()
        sys.exit(0)
    if "--window" in sys.argv:
        # Stay alive for N minutes and check again whenever sites become due. The next scheduled run queues behind this one,
        # so checking carries on without gaps even if GitHub's own cron is late. Public repositories have unlimited Actions minutes.
        minutes = int(sys.argv[sys.argv.index("--window") + 1])
        end = time.time() + minutes * 60
        while True:
            try:
                n = run_once(budget_seconds=max(60, min(900, int(end - time.time()))))
            except Exception as e:
                print("Execution loop error:", e)
                n = 0
            if time.time() + 240 > end:
                break
            time.sleep(60 if n else 240)
        sys.exit(0)
    if "--loop" in sys.argv:
        while True:
            try:
                run_once()
            except Exception as e:
                print("Execution loop error:", e)
            time.sleep(60)
    else:
        run_once()
