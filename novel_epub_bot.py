#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Novel -> EPUB Telegram Bot (sirf standard library, ek hi file) [v6 - single message flow]

Chalane ke liye: python novel_epub_bot.py (Pydroid3: bas Run dabao)

v6 me kya naya hai (video jaisa flow):
* Link bhejo -> ek banner-wala message banta hai (scan -> range/options -> progress)
* "Create EPUB Book" dabate hi wahi message progress me badal jata hai
* EPUB ready hote hi usi message ki jagah file aa jati hai (editMessageMedia)
* BANNER khali ho to bot khud ek default banner bana leta hai (photo message zaroori hai)
"""
from __future__ import annotations

import html
import http.client
import ipaddress
import json
import os
import queue
import random
import re
import shutil
import socket
import struct
import sys
import tempfile
import threading
import time
import traceback
import unicodedata
import uuid
import zipfile
import zlib
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from html.parser import HTMLParser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib import error, parse, request

# ============================== CONFIG ==============================
BOT_TOKEN = ""  # Render par Environment Variable TELEGRAM_BOT_TOKEN me daalo (yahan mat likho)
ALLOWED_USERS = {8049392574}  # Admin ID added
WORKERS = int(os.environ.get("WORKERS", 24))  # Render free (0.1 CPU, 512MB) ke liye 24; zyada CPU ho to badhao
HOST_MAX = int(os.environ.get("HOST_MAX", 48))  # ek SITE par sab jobs milake max ek saath requests (alag site = alag limit)
MIN_WORKERS = 4  # block aane par bhi kam se kam itne chalenge
MAX_JOBS_PER_CHAT = 3  # ek chat me ek saath max EPUB jobs
MAX_JOBS_TOTAL = 5  # poore bot me ek saath max jobs
MAX_CHAPTERS = int(os.environ.get("MAX_CHAPTERS", 3000))  # 512MB RAM ke liye
MAX_PAGE_BYTES = 8 * 1024 * 1024
TIMEOUT = 15  # ek request ka timeout (sec)
RETRIES = 3  # ek page ke liye network retries
CH_TRIES = 2  # ek chapter ke liye poori try (download + parse)
REPAIR_PASSES = 2  # fail chapters ko baad me dobara try karne ke round
MIN_TOC = 5
TG_LIMIT = 49 * 1024 * 1024
BANNER = ""  # Apni photo: image ka URL ya phone par file ka path (jaise "/sdcard/banner.jpg"). Khali = bot khud banner banata hai
SUPPORT_URL = ""  # "https://t.me/yourname" daalo to "Contact support" button dikhega. Khali = nahi dikhega
USER_AGENTS = (
    "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 14; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36",
)
RETRY_CODES = {403, 408, 409, 425, 429, 500, 502, 503, 504, 520, 521, 522, 523, 524}
HARD_CODES = {403, 429, 503, 520, 521, 522, 523, 524}

# ---- IPv4 pehle: mobile network par broken IPv6 ki wajah se 30-120 sec hang hota tha
_orig_getaddrinfo = socket.getaddrinfo


def _ipv4_first(host, port, family=0, type=0, proto=0, flags=0):
    res = _orig_getaddrinfo(host, port, family, type, proto, flags)
    return sorted(res, key=lambda r: r[0] != socket.AF_INET)


socket.getaddrinfo = _ipv4_first

# ---- thread stack: Android par chhota default stack crash karta hai
try:
    threading.stack_size(2 * 1024 * 1024)
except (ValueError, RuntimeError):
    pass


class FetchError(Exception):
    pass


class ParseError(Exception):
    pass


class Cancelled(Exception):
    pass


# ============================== 0. SMART SPEED LIMITER (per site) ==============================
class Limiter:
    """Ek site par ek saath kitne requests chalein. Site 429/403 de to aadha, sab theek ho to tezi se wapas badhao."""

    def __init__(self, maxn, minn):
        self.max, self.min, self.limit = maxn, minn, maxn
        self.active, self.streak = 0, 0
        self.pause_until, self.last_cut = 0.0, 0.0
        self.cv = threading.Condition()

    def acquire(self):
        with self.cv:
            while self.active >= self.limit or time.monotonic() < self.pause_until:
                self.cv.wait(0.05)
            self.active += 1

    def release(self):
        with self.cv:
            self.active -= 1
            self.cv.notify_all()

    def good(self):
        with self.cv:
            self.streak += 1
            if self.streak >= 3 and self.limit < self.max:
                self.limit = min(self.max, self.limit + 4)
                self.streak = 0
                self.cv.notify_all()

    def slow_down(self, wait=0.0, hard=True):
        with self.cv:
            now = time.monotonic()
            if hard:
                if now - self.last_cut > 1.5:  # ek saath kai threads fail hon to baar-baar aadha na ho
                    self.limit = max(self.min, self.limit // 2)
                    self.last_cut = now
                self.pause_until = max(self.pause_until, now + wait)
            else:
                self.limit = max(self.min, self.limit - 1)
            self.streak = 0

    def cap(self, n):
        with self.cv:
            self.limit = max(self.min, min(self.limit, n))


_LIMITERS = {}
_LIM_LOCK = threading.Lock()


def _host_key(url):
    h = (parse.urlparse(url).hostname or "").lower()
    return h[4:] if h.startswith("www.") else h


def get_limiter(url):
    """Har site (host) ka apna limiter - alag-alag novels alag sites par ho to ek dusre ko slow nahi karte."""
    key = _host_key(url)
    with _LIM_LOCK:
        lim = _LIMITERS.get(key)
        if lim is None:
            lim = _LIMITERS[key] = Limiter(HOST_MAX, MIN_WORKERS)
        return lim


# ============================== 1. MINI DOM ==============================
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta",
        "param", "source", "track", "wbr"}
AUTOCLOSE = {"li", "p", "dt", "dd", "tr", "td", "th", "option"}
MAX_DEPTH = 200
_XML_BAD = re.compile("[\x00-\x08\x0b\x0c\x0e-\x1f\ufffe\uffff]")
_SLIM = re.compile(r"<!--.*?-->|<(script|style|noscript|svg|iframe)\b[^>]*>.*?</\1\s*>", re.I | re.S)


def slim_html(t):
    """Parse se pehle bhaari faltu cheezein hata do - parse bahut tez ho jata hai."""
    return _SLIM.sub("", t)


class Node:
    __slots__ = ("tag", "attrs", "children", "parent", "data")

    def __init__(self, tag, attrs=None, data=""):
        self.tag = tag
        self.attrs = dict(attrs or {})
        self.children = []
        self.parent = None
        self.data = data

    @property
    def is_text(self):
        return self.tag == "#text"

    def get(self, name, default=""):
        return self.attrs.get(name, default)

    def append(self, child):
        child.parent = self
        self.children.append(child)
        return child

    def remove(self):
        if self.parent is not None:
            self.parent.children = [c for c in self.parent.children if c is not self]
            self.parent = None

    def iter(self):
        stack = list(reversed(self.children))
        while stack:
            n = stack.pop()
            if n.is_text:
                continue
            yield n
            stack.extend(reversed(n.children))

    def text(self):
        out, stack = [], list(reversed(self.children))
        while stack:
            n = stack.pop()
            if n.is_text:
                out.append(n.data)
            else:
                stack.extend(reversed(n.children))
        return "".join(out)

    def select(self, selector):
        return _compile_selector(selector).run(self)

    def select_one(self, selector):
        return _compile_selector(selector).first(self)


class _Builder(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Node("#document")
        self.stack = [self.root]

    def _open(self, tag, attrs):
        tag = tag.lower()
        if tag in AUTOCLOSE and self.stack[-1].tag == tag:
            self.stack.pop()
        node = Node(tag, {k.lower(): (v or "") for k, v in attrs})
        self.stack[-1].append(node)
        if tag not in VOID and len(self.stack) < MAX_DEPTH:
            self.stack.append(node)
            return True
        return False

    def handle_starttag(self, tag, attrs):
        self._open(tag, attrs)

    def handle_startendtag(self, tag, attrs):
        if self._open(tag, attrs):
            self.stack.pop()

    def handle_endtag(self, tag):
        tag = tag.lower()
        if tag in VOID:
            return
        for i in range(len(self.stack) - 1, 0, -1):
            if self.stack[i].tag == tag:
                del self.stack[i:]
                return

    def handle_data(self, data):
        top = self.stack[-1]
        if top.children and top.children[-1].is_text:
            top.children[-1].data += data
        else:
            top.append(Node("#text", data=data))


def parse_html(text):
    b = _Builder()
    b.feed(text)
    b.close()
    return b.root


# ---- CSS selectors: tag #id .class [attr op val], ' ' '>' ','
_TOKEN = re.compile(r"""#[\w-]+|\.[\w-]+|\[[^\]]+\]""")
_ATTR = re.compile(r"""\[\s*([\w:-]+)\s*(?:([~|^$*]?=)\s*(?:"([^"]*)"|'([^']*)'|([^\]\s]*)))?\s*\]""")


def _attr_check(name, op, val):
    def check(n):
        if name not in n.attrs:
            return False
        v = n.attrs[name]
        if op is None:
            return True
        return {"=": v == val, "~=": val in v.split(), "^=": v.startswith(val),
                "$=": v.endswith(val), "*=": val in v, "|=": v == val or v.startswith(val + "-")}.get(op, False)

    return check


def _compound(s):
    m = re.match(r"(?:\*|[A-Za-z][\w-]*)?", s)
    tag, rest, pos, checks = (m.group(0) or "").lower(), s[m.end():], 0, []
    for t in _TOKEN.finditer(rest):
        if t.start() != pos:
            raise ValueError(f"Unsupported selector: {s!r}")
        pos = t.end()
        x = t.group(0)
        if x[0] == "#":
            checks.append(lambda n, v=x[1:]: n.get("id") == v)
        elif x[0] == ".":
            checks.append(lambda n, v=x[1:]: v in n.get("class").split())
        else:
            am = _ATTR.fullmatch(x)
            if not am:
                raise ValueError(f"Bad attribute selector: {x!r}")
            val = next((g for g in am.groups()[2:] if g is not None), "")
            checks.append(_attr_check(am.group(1).lower(), am.group(2), val))
    if pos != len(rest):
        raise ValueError(f"Unsupported selector: {s!r}")
    return tag, checks


def _match_compound(n, comp):
    tag, checks = comp
    if n.is_text or n.tag == "#document":
        return False
    if tag and tag != "*" and n.tag != tag:
        return False
    return all(c(n) for c in checks)


def _match_chain(n, parts, i):
    comb, comp = parts[i]
    if not _match_compound(n, comp):
        return False
    if i == 0:
        return True
    p = n.parent
    if comb == ">":
        return p is not None and _match_chain(p, parts, i - 1)
    while p is not None:
        if _match_chain(p, parts, i - 1):
            return True
        p = p.parent
    return False


class _Selector:
    def __init__(self, groups):
        self.groups = groups

    def matches(self, n):
        return any(_match_chain(n, g, len(g) - 1) for g in self.groups)

    def run(self, root):
        return [n for n in root.iter() if self.matches(n)]

    def first(self, root):
        for n in root.iter():
            if self.matches(n):
                return n
        return None


@lru_cache(maxsize=256)
def _compile_selector(selector):
    groups = []
    for part in re.split(r",(?![^\[]*\])", selector):
        part = re.sub(r"\s>\s*", " > ", part.strip())
        if not part:
            continue
        parts, comb = [], " "
        for tok in re.split(r"\s+(?![^\[]*\])", part):
            if tok == ">":
                comb = ">"
                continue
            parts.append((comb, _compound(tok)))
            comb = " "
        groups.append(parts)
    if not groups:
        raise ValueError("Empty selector")
    return _Selector(groups)


# ---- XHTML output (bina recursion)
def esc(s):
    return _XML_BAD.sub("", html.escape(s, quote=False))


def to_xhtml(root):
    out, stack = [], [root]
    while stack:
        n = stack.pop()
        if isinstance(n, str):  # closing tag
            out.append(n)
        elif n.is_text:
            out.append(esc(n.data))
        elif n.tag in VOID:
            out.append(f"<{n.tag}/>")
        else:
            out.append(f"<{n.tag}>")
            stack.append(f"</{n.tag}>")
            stack.extend(reversed(n.children))
    return "".join(out)


# ============================== 2. CLEANER (bina recursion) ==============================
KEEP = {"p", "br", "hr", "b", "i", "u", "em", "strong", "s", "strike", "sub", "sup", "blockquote",
        "pre", "ul", "ol", "li", "div", "table", "thead", "tbody", "tr", "td", "th",
        "h1", "h2", "h3", "h4", "h5", "h6"}
DROP = {"script", "style", "iframe", "noscript", "form", "object", "embed", "link", "meta", "canvas",
        "button", "input", "select", "textarea", "svg", "audio", "video", "head", "title", "base",
        "img", "ins", "nav"}
PRUNE = {"p", "div", "li", "b", "i", "u", "em", "strong", "blockquote", "ul", "ol", "table", "tr", "td"}
JUNK = ".adsbygoogle, .ads, .code-block, .chapter-nav, .comments, #comments"


def clean(root):
    """Sirf safe tags rakho, saare attributes hatao, baaki tags unwrap."""
    stack = [root]
    while stack:
        node = stack.pop()
        out, todo = [], list(reversed(node.children))
        while todo:
            c = todo.pop()
            if c.is_text:
                out.append(c)
            elif c.tag in DROP:
                continue
            elif c.tag in KEEP:
                c.attrs = {}
                out.append(c)
                stack.append(c)
            else:  # unwrap: iske bachche isi level par process honge
                todo.extend(reversed(c.children))
        for c in out:
            c.parent = node
        node.children = out


def prune(root):
    nodes = [root] + list(root.iter())
    for node in reversed(nodes):  # bachche pehle, parent baad me
        keep = []
        for c in node.children:
            if (c.tag in PRUNE and not c.text().replace("\xa0", " ").strip()
                    and not any(d.tag == "hr" for d in c.iter())):
                continue
            keep.append(c)
        node.children = keep


# ============================== 3. HTTP (keep-alive, cookies, redirects) ==============================
@lru_cache(maxsize=512)
def _host_is_public(host, port):
    try:
        infos = socket.getaddrinfo(host, port, proto=socket.IPPROTO_TCP)
    except (socket.gaierror, UnicodeError):
        raise FetchError("Host resolve nahi hua") from None
    for info in infos:
        ip = ipaddress.ip_address(info[4][0].split("%")[0])
        if ip.version == 6 and ip.ipv4_mapped:
            ip = ip.ipv4_mapped
        if not ip.is_global:
            raise FetchError("Private/local address allowed nahi hai")
    return True


def check_public(url):
    try:
        p = parse.urlparse(url)
        if p.scheme not in ("http", "https") or not p.hostname:
            raise FetchError("Sirf http/https link chalega")
        _host_is_public(p.hostname, p.port or (443 if p.scheme == "https" else 80))
    except ValueError:
        raise FetchError("Link galat hai") from None


_tls = threading.local()
COOKIES = {}  # host -> {name: value}
_REDIRECTS = (301, 302, 303, 307, 308)
_SAFE = "/%:@!$&'()*+,;=-._~"
_STALE = (http.client.BadStatusLine, http.client.CannotSendRequest, ConnectionError)


def _pool():
    p = getattr(_tls, "pool", None)
    if p is None:
        p = _tls.pool = {}
        _tls.ua = random.choice(USER_AGENTS)  # ek thread = ek browser (cookies ke saath mel khata hai)
    return p


def _get_once(url, headers):
    p = parse.urlparse(url)
    key = (p.scheme, p.hostname, p.port)
    path = parse.quote(p.path or "/", safe=_SAFE)
    if p.query:
        path += "?" + parse.quote(p.query, safe=_SAFE + "?")
    pool = _pool()
    for attempt in (0, 1):
        c = pool.get(key)
        reused = c is not None
        if c is None:
            cls = http.client.HTTPSConnection if p.scheme == "https" else http.client.HTTPConnection
            c = pool[key] = cls(p.hostname, p.port, timeout=TIMEOUT)
        try:
            c.request("GET", path, headers=headers)
            r = c.getresponse()
            data = r.read(MAX_PAGE_BYTES + 1)
            if r.will_close or len(data) > MAX_PAGE_BYTES:
                c.close()
                pool.pop(key, None)
            return r.status, r.headers, data
        except (http.client.HTTPException, OSError) as e:
            try:
                c.close()
            except Exception:  # noqa: BLE001
                pass
            pool.pop(key, None)
            if reused and attempt == 0 and isinstance(e, _STALE):
                continue  # purana keep-alive connection toot gaya tha, naya khol ke dobara
            raise


def _get_following(url, base_headers):
    for _ in range(6):
        p = parse.urlparse(url)
        headers = dict(base_headers)
        ck = COOKIES.get(p.hostname)
        if ck:
            headers["Cookie"] = "; ".join(f"{k}={v}" for k, v in list(ck.items()))
        status, hdrs, data = _get_once(url, headers)
        for sc in hdrs.get_all("Set-Cookie") or ():
            nv = sc.split(";", 1)[0]
            if "=" in nv:
                k, v = nv.split("=", 1)
                COOKIES.setdefault(p.hostname, {})[k.strip()] = v.strip()
        loc = hdrs.get("Location")
        if status in _REDIRECTS and loc:
            url = parse.urljoin(url, loc).split("#")[0]
            check_public(url)
            continue
        return status, hdrs, data
    raise FetchError("Bahut zyada redirect")


def _inflate(data, enc):
    if enc not in ("gzip", "deflate"):
        return data
    for wbits in ((16 + zlib.MAX_WBITS,) if enc == "gzip" else (zlib.MAX_WBITS, -zlib.MAX_WBITS)):
        try:
            out = zlib.decompressobj(wbits).decompress(data, MAX_PAGE_BYTES + 1)
        except zlib.error:
            continue
        if len(out) > MAX_PAGE_BYTES:
            raise FetchError("Page bahut bada hai")
        return out
    raise FetchError("Compressed data kharab hai")


def _retry_after(h):
    try:
        return float(h.get("Retry-After", "") or 0)
    except (ValueError, AttributeError):
        return 0.0


def fetch(url, retries=RETRIES):
    check_public(url)
    p = parse.urlparse(url)
    lim = get_limiter(url)  # is site ka limiter (dusri sites ka asar nahi)
    _pool()
    headers = {
        "User-Agent": _tls.ua,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Encoding": "gzip, deflate", "Accept-Language": "en-US,en;q=0.9",
        "Referer": f"{p.scheme}://{p.netloc}/"}
    last = None
    for attempt in range(retries + 1):
        try:
            lim.acquire()
            try:
                status, hdrs, data = _get_following(url, headers)
            finally:
                lim.release()
        except FetchError:
            raise
        except (http.client.HTTPException, OSError, ValueError) as e:
            last = type(e).__name__
            if isinstance(e, (socket.timeout, TimeoutError, ConnectionError)):
                lim.slow_down(hard=False)
            time.sleep(min(0.3 * (2 ** attempt), 4) + random.random() * 0.3)
            continue
        if 200 <= status < 300:
            if len(data) > MAX_PAGE_BYTES:
                raise FetchError("Page bahut bada hai")
            out = _inflate(data, hdrs.get("Content-Encoding", "").lower())
            lim.good()
            return out, hdrs.get("Content-Type", "")
        last = f"HTTP {status}"
        if status not in RETRY_CODES:
            break
        if status in HARD_CODES:
            lim.slow_down(min(max(_retry_after(hdrs), 2 * (attempt + 1)), 30))
        time.sleep(min(0.3 * (2 ** attempt), 4) + random.random() * 0.3)
    raise FetchError(f"Download fail: {last}")


def decode(data, ctype=""):
    if data.startswith(b"\xef\xbb\xbf"):
        return data[3:].decode("utf-8", "replace")
    enc = None
    m = re.search(r"charset=([\w-]+)", ctype or "", re.I)
    if m:
        enc = m.group(1)
    else:
        m = re.search(rb"""<meta[^>]+charset=["']?([\w-]+)""", data[:4096], re.I)
        if m:
            enc = m.group(1).decode("ascii", "ignore")
    for e in (enc, "utf-8"):
        if e:
            try:
                return data.decode(e)
            except (LookupError, UnicodeDecodeError):
                pass
    return data.decode("cp1252", "replace")


def get_dom(url):
    return parse_html(slim_html(decode(*fetch(url))))


# ============================== 4. NOVEL LOGIC ==============================
def clean_text(s):
    return re.sub(r"\s+", " ", s.replace("\xa0", " ")).strip()


@dataclass
class Ref:
    title: str
    url: str


@dataclass
class Chapter:
    title: str
    body: str
    ok: bool = True


def _norm_host(url):
    h = (parse.urlparse(url).netloc or "").lower()
    return h[4:] if h.startswith("www.") else h


def _num(text, href):
    m = re.findall(r"\d+(?:\.\d+)?", text or "")
    if m:
        return float(m[0])
    m = re.findall(r"\d+(?:\.\d+)?", href or "")
    return float(m[-1]) if m else None


def find_toc(dom, url):
    """Page par sabse badi 'chapter links ki list' dhoondo (ek hi folder ke links, ek hi container me)."""
    host = _norm_host(url)
    groups = {}
    for a in dom.select("a[href]"):
        href = a.get("href").strip()
        if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
            continue
        full = parse.urljoin(url, href).split("#")[0]
        if _norm_host(full) != host or not full.startswith("http"):
            continue
        dirpath = parse.urlparse(full).path.rsplit("/", 1)[0]
        anc = a
        for lvl in (1, 2, 3):
            anc = anc.parent
            if anc is None or anc.tag == "#document":
                break
        groups.setdefault((lvl, anc, dirpath), {}).setdefault(full, a)
    best, best_key = None, None
    for key, links in groups.items():
        n = len(links)
        if n < MIN_TOC:
            continue
        likes = sum(1 for u, a in links.items() if re.search(r"\d", a.text() + u))
        if likes < 0.5 * n:
            continue
        rank = (n, -key[0])
        if best is None or rank > best_key:
            best, best_key = links, rank
    if best is None:
        return []
    items = [(clean_text(a.text())[:150], u) for u, a in best.items()]
    nums = [_num(t, u) for t, u in items]
    known = [x for x in nums if x is not None]
    if len(known) >= 3 and known[0] > known[-1]:  # newest-first list -> ulta karo
        items.reverse()
    return [Ref(t or f"Chapter {i}", u) for i, (t, u) in enumerate(items, 1)]


_NEXT_TEXT = re.compile(r"^(next(\s+chapter|\s+ch\.?)?|[>»›→]+)\s*[>»›→]*$", re.I)
_NEXT_ID = re.compile(r"(?<![a-z])next(?![a-z])")
_FIRST_TEXT = re.compile(r"read\s(now|first|from\sstart)|start\sreading|first\schapter|^(chapter|ch\.?)\s0*1\b", re.I)


def _ok_href(h):
    h = (h or "").strip()
    return bool(h) and not h.startswith(("#", "javascript:", "mailto:"))


def find_next(dom, url):
    for n in dom.select("link[rel=next], a[rel=next]"):
        if _ok_href(n.get("href")):
            return parse.urljoin(url, n.get("href"))
    for a in dom.select("a[href]"):
        if not _ok_href(a.get("href")):
            continue
        t = clean_text(a.text())
        ident = (a.get("id") + " " + a.get("class")).lower()
        if (len(t) <= 30 and _NEXT_TEXT.match(t)) or _NEXT_ID.search(ident):
            u = parse.urljoin(url, a.get("href")).split("#")[0]
            if u != url:
                return u
    return None


def find_first_chapter(dom, url):
    for a in dom.select("a[href]"):
        if _ok_href(a.get("href")) and _FIRST_TEXT.search(clean_text(a.text())):
            return parse.urljoin(url, a.get("href")).split("#")[0]
    return None


def page_title(dom):
    h = dom.select_one("h1")
    og = dom.select_one('meta[property="og:title"]')
    t = dom.select_one("title")
    return clean_text((h.text() if h else "") or (og.get("content") if og else "")
                      or (t.text() if t else ""))[:150]


def book_info(dom, url):
    au = dom.select_one('meta[name="author"]')
    ar = dom.select_one("a[rel=author]")
    author = clean_text((au.get("content") if au else "") or (ar.text() if ar else "")) or "Unknown"
    h = dom.select_one("html")
    return {"title": plain(clean_book_title(page_title(dom))) or "Novel", "author": author[:100],
            "lang": (h.get("lang") if h and h.get("lang") else "en"), "url": url}


_TITLE_JUNK = re.compile(r"\s*(?:[-|–—]\s*)?(?:novel\sphoenix|read\s+online|all\s+chapters|chapters?\s+list)\s*$", re.I)
_TITLE_TAIL = re.compile(r"\s*(?:novel\s+)?(?:chapters?|chapter\s+list)\s*$", re.I)


def plain(s):
    """Accent hatao (Pokémon -> Pokemon) aur : ? " jaise symbols hatao -> saaf naam."""
    s = unicodedata.normalize("NFKD", s)
    s = "".join(ch for ch in s if not unicodedata.combining(ch))
    s = re.sub(r'[\\/:*?"<>|\x00-\x1f]+', " ", s)
    return re.sub(r"\s+", " ", s).strip()


def clean_book_title(t):
    """'Xyz Novel Chapters - Novel Phoenix' -> 'Xyz'"""
    t = clean_text(t)
    for _ in range(3):
        t2 = _TITLE_JUNK.sub("", t)
        t2 = _TITLE_TAIL.sub("", t2)
        t2 = re.sub(r"\s+novel$", "", t2, flags=re.I).strip(" -|–—:")
        if t2 == t:
            break
        t = t2
    return t or "Novel"


_CH_TITLE = re.compile(r"(?:chapter|chap\.?|ch\.?|episode|ep\.?)\s*[-:#]?\s*(\d+)", re.I)
CH_URL = re.compile(r"(?:chapter|chap|ch|episode|ep)[-/]?(\d+)", re.I)


def chapter_no(ref):
    for rx, s in ((_CH_TITLE, ref.title), (CH_URL, parse.urlparse(ref.url).path)):
        m = rx.search(s or "")
        if m:
            return int(m.group(1))
    return None


def range_label(refs, url, first, full_n):
    """'[ 101-200 ]' - asli chapter numbers se, warna ?page=N se hisaab."""
    a, b = chapter_no(refs[0]), chapter_no(refs[-1])
    if a is None or b is None or b < a or (b - a + 1) > len(refs) * 3:
        q = parse.parse_qs(parse.urlparse(url).query)
        pg = q.get("page", q.get("p", ["1"]))[0]
        page = int(pg) if pg.isdigit() and int(pg) > 0 else 1
        a = (page - 1) * full_n + first
        b = a + len(refs) - 1
    return f"[ {a}-{b} ]"


CONTENT_SELECTORS = ("#chr-content", "#chapter-content", ".chapter-content", ".reading-content",
                     "#storytext", "#chapterText", ".chapter-body", "#chapter-body", ".chapter__content",
                     ".text-left", "#content", ".entry-content", ".post-content", ".prose",
                     "article", "main")
_BAD_CLS = re.compile(r"comment|sidebar|footer|menu|widget|related|share|(^|[\s_-])nav", re.I)
_BLOCK_RE = re.compile(r"just a moment|attention required|access denied|verify you are human|"
                       r"too many requests|rate limit|checking your browser|temporarily unavailable", re.I)


def smart_detect(dom):
    """Jis element me sabse zyada seedha text (paragraphs) ho wahi chapter hai."""
    best, score = None, 0
    for n in dom.iter():
        if n.tag in ("script", "style", "nav", "footer", "header", "aside", "form"):
            continue
        if _BAD_CLS.search(n.get("class") + " " + n.get("id")):
            continue
        s = 0
        for c in n.children:
            if c.is_text:
                s += len(c.data.strip())
            elif c.tag == "p":
                s += len(clean_text(c.text()))
        if s > score:
            best, score = n, s
    return best


def _index_dom(dom):
    """Ek hi pass me id/class/tag ka pehla element yaad rakho (pehle 15 baar DOM ghoomta tha)."""
    ids, cls, tags = {}, {}, {}
    for n in dom.iter():
        a = n.attrs
        v = a.get("id")
        if v and v not in ids:
            ids[v] = n
        v = a.get("class")
        if v:
            for k in v.split():
                if k not in cls:
                    cls[k] = n
        if n.tag not in tags:
            tags[n.tag] = n
    return ids, cls, tags


def extract_content(dom):
    ids, cls, tags = _index_dom(dom)
    t = tags.get("title")
    if t and _BLOCK_RE.search(t.text()) and len(clean_text(dom.text())) < 3000:
        raise ParseError("Site ne block/limit page diya")  # retry hoga
    node = None
    for sel in CONTENT_SELECTORS:
        if sel[0] == "#":
            n = ids.get(sel[1:])
        elif sel[0] == ".":
            n = cls.get(sel[1:])
        else:
            n = tags.get(sel)
        if n is not None and len(clean_text(n.text())) >= 150:
            node = n
            break
    if node is None:
        node = smart_detect(dom)
    if node is None or len(clean_text(node.text())) < 20:
        body = tags.get("body")  # last resort
        if body is not None and len(clean_text(body.text())) >= 150:
            node = body
    if node is None or len(clean_text(node.text())) < 20:
        raise ParseError("Chapter ka text nahi mila")
    return node


def build_body(title, node):
    wrap = Node("div")
    wrap.append(node)
    for x in wrap.select(JUNK):
        x.remove()
    clean(wrap)
    tl = title.lower()
    for h in wrap.select("h1, h2, h3, h4"):
        if clean_text(h.text()).lower() == tl:
            h.remove()
    prune(wrap)
    if not clean_text(wrap.text()):
        raise ParseError("Chapter khali hai")
    return f"<h2>{esc(title)}</h2>" + "".join(to_xhtml(c) for c in wrap.children)


def _failed(title, why):
    return Chapter(title, f"<h2>{esc(title)}</h2><p>[Chapter load nahi hua: {esc(str(why)[:150])}]</p>", False)


def make_chapter(title, dom):
    try:
        return Chapter(title, build_body(title, extract_content(dom)))
    except ParseError as e:
        return _failed(title, e)


def fetch_chapter(ref, tries=CH_TRIES, cancel=None):
    """Download + parse, fail ho to thoda ruk ke dobara (har baar naya page)."""
    why = None
    for i in range(tries):
        if cancel is not None and cancel.is_set():
            break
        try:
            return Chapter(ref.title, build_body(ref.title, extract_content(get_dom(ref.url))))
        except FetchError as e:
            why = e
            if "HTTP 404" in str(e) or "HTTP 410" in str(e):
                break  # chapter hai hi nahi, retry bekaar
        except Exception as e:  # noqa: BLE001 (ek chapter poora kaam na roke)
            why = e
        time.sleep(min(0.5 * (i + 1), 3) + random.random() * 0.5)
    return _failed(ref.title, why or "cancel")


# ============================== 5. EPUB ==============================
def _page(title, body, lang):
    lg = html.escape(lang, quote=True)
    return ('<?xml version="1.0" encoding="utf-8"?>\n<!DOCTYPE html>\n'
            f'<html xmlns="http://www.w3.org/1999/xhtml" xmlns:epub="http://www.idpf.org/2007/ops" lang="{lg}" xml:lang="{lg}">\n'
            f'<head><meta charset="utf-8"/><title>{esc(title)}</title>'
            '<link rel="stylesheet" type="text/css" href="styles.css"/></head>\n'
            f'<body>\n{body}\n</body></html>')


CSS = "body{margin:5%;line-height:1.5}\nh1,h2{text-align:center}\np{margin:.6em 0}\n"


def pack_epub(info, chapters, out):
    lang = info["lang"]
    ident = "urn:uuid:" + str(uuid.uuid5(uuid.NAMESPACE_URL, info["url"]))
    mod = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    names = [f"Section{i:04d}.xhtml" for i in range(1, len(chapters) + 1)]
    manifest = ['<item id="nav" href="nav.xhtml" media-type="application/xhtml+xml" properties="nav"/>',
                '<item id="ncx" href="toc.ncx" media-type="application/x-dtbncx+xml"/>',
                '<item id="css" href="styles.css" media-type="text/css"/>']
    manifest += [f'<item id="s{i}" href="{n}" media-type="application/xhtml+xml"/>' for i, n in enumerate(names, 1)]
    spine = "".join(f'<itemref idref="s{i}"/>' for i in range(1, len(names) + 1))
    opf = ('<?xml version="1.0" encoding="utf-8"?>\n<package xmlns="http://www.idpf.org/2007/opf" '
           'unique-identifier="bookid" version="3.0">\n<metadata xmlns:dc="http://purl.org/dc/elements/1.1/">\n'
           f'<dc:identifier id="bookid">{ident}</dc:identifier><dc:title>{esc(info["title"])}</dc:title>'
           f'<dc:creator>{esc(info["author"])}</dc:creator><dc:language>{esc(lang)}</dc:language>'
           f'<meta property="dcterms:modified">{mod}</meta></metadata>\n<manifest>\n' + "\n".join(manifest) +
           f'\n</manifest>\n<spine toc="ncx">{spine}</spine>\n</package>')
    nav_li = "".join(f'<li><a href="{n}">{esc(c.title)}</a></li>' for n, c in zip(names, chapters))
    nav = _page("Contents", f'<nav epub:type="toc" id="toc"><h1>Contents</h1><ol>{nav_li}</ol></nav>', lang)
    points = "".join(f'<navPoint id="n{i}" playOrder="{i}"><navLabel><text>{esc(c.title)}</text></navLabel>'
                     f'<content src="{n}"/></navPoint>' for i, (n, c) in enumerate(zip(names, chapters), 1))
    ncx = ('<?xml version="1.0" encoding="utf-8"?>\n<ncx xmlns="http://www.daisy.org/z3986/2005/ncx/" version="2005-1">'
           f'<head><meta name="dtb:uid" content="{ident}"/><meta name="dtb:depth" content="1"/></head>'
           f'<docTitle><text>{esc(info["title"])}</text></docTitle><navMap>{points}</navMap></ncx>')
    container = ('<?xml version="1.0"?>\n<container version="1.0" xmlns="urn:oasis:names:tc:opendocument:xmlns:container">'
                 '<rootfiles><rootfile full-path="OEBPS/content.opf" media-type="application/oebps-package+xml"/>'
                 '</rootfiles></container>')

    def b(s):
        return s.encode("utf-8", "replace")

    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED, compresslevel=1) as z:  # level 1 = sabse tez
        z.writestr(zipfile.ZipInfo("mimetype"), "application/epub+zip", compress_type=zipfile.ZIP_STORED)
        z.writestr("META-INF/container.xml", b(container))
        for name, text in (("content.opf", opf), ("nav.xhtml", nav), ("toc.ncx", ncx), ("styles.css", CSS)):
            z.writestr(f"OEBPS/{name}", b(text))
        for n, c in zip(names, chapters):
            z.writestr(f"OEBPS/{n}", b(_page(c.title, c.body, lang)))
    return out


_PUNCT = str.maketrans({"’": "'", "‘": "'", "“": '"', "”": '"', "–": "-", "—": "-",
                        "…": "...", "\u00a0": " "})


def ascii_clean(s):
    """'Pokémon: The X' -> 'Pokemon The X' (accent hatao, : jaise bure chars hatao, space/[ ]/- rakho)."""
    s = unicodedata.normalize("NFKD", s.translate(_PUNCT))
    s = "".join(ch for ch in s if not unicodedata.combining(ch)).encode("ascii", "ignore").decode()
    s = re.sub(r'[\/\\:*?"<>|\x00-\x1f]+', "", s)
    return re.sub(r"\s+", " ", s).strip(" .")


def safe_filename(s, limit=80):
    return (ascii_clean(s) or "novel")[:limit].strip(" .")


# Telegram server upload par file name ke ASCII space / [ ] - ( ) , . ' ! sab ko '_' bana deta hai
# (letters/digits aur non-ASCII chars rehte hain). Isliye inhe dikhne me same Unicode chars se badal dete hain.
FANCY_FILENAME = True
_FANCY = str.maketrans({" ": "\u2002", "[": "\uff3b", "]": "\uff3d", "-": "\u2013", "(": "\uff08",
                        ")": "\uff09", ",": "\uff0c", "'": "\u2019", "!": "\uff01", "&": "\uff06",
                        ".": "\u2024", "#": "\uff03", "+": "\uff0b", "=": "\uff1d", ";": "\uff1b",
                        "@": "\uff20", "~": "\uff5e", "$": "\uff04", "%": "\uff05", "^": "\uff3e"})


def tg_filename(name):
    """Extension (.epub) isme nahi aata - wo baad me joda jata hai."""
    return name.translate(_FANCY) if FANCY_FILENAME else name


# ============================== 5b. DEFAULT BANNER (PNG, bina library) ==============================
def make_banner_png(w=800, h=320):
    """Gradient banner. Photo message hona zaroori hai taaki baad me wahi message EPUB file ban sake."""
    rows = []
    for y in range(h):
        row = bytearray([0])
        for x in range(w):
            t = (x / w) * 0.6 + (y / h) * 0.4
            row += bytes((int(32 + 90 * t), int(24 + 50 * (1 - t)), int(96 + 120 * (1 - t))))
        rows.append(bytes(row))

    def chunk(tag, data):
        c = struct.pack(">I", len(data)) + tag + data
        return c + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)

    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(b"".join(rows), 6)) + chunk(b"IEND", b""))


# ============================== 6. TELEGRAM ==============================
class TelegramError(Exception):
    def __init__(self, msg, retry_after=0):
        super().__init__(msg)
        self.retry_after = retry_after


def _multipart(fields, files):
    b = uuid.uuid4().hex
    out = []
    for k, v in fields.items():
        out.append(f'--{b}\r\nContent-Disposition: form-data; name="{k}"\r\n\r\n{v}\r\n'.encode())
    for k, (fname, data, mime) in files.items():
        fname = re.sub(r'[\r\n"]', "_", fname)
        out.append(f'--{b}\r\nContent-Disposition: form-data; name="{k}"; filename="{fname}"\r\n'
                   f"Content-Type: {mime}\r\n\r\n".encode() + data + b"\r\n")
    out.append(f"--{b}--\r\n".encode())
    return b"".join(out), f"multipart/form-data; boundary={b}"


class TelegramAPI:
    def __init__(self, token):
        self.token = token
        self.base = "https://api.telegram.org"

    def call(self, method, params=None, files=None, timeout=20):
        if files:
            body, ctype = _multipart({k: str(v) for k, v in (params or {}).items()}, files)
        else:
            body, ctype = json.dumps(params or {}).encode(), "application/json"
        req = request.Request(f"{self.base}/bot{self.token}/{method}", data=body, headers={"Content-Type": ctype})
        try:
            with request.urlopen(req, timeout=timeout) as r:
                data = json.loads(r.read())
        except error.HTTPError as e:
            try:
                data = json.loads(e.read())
            except ValueError:
                raise TelegramError(f"{method}: HTTP {e.code}") from None
        except (error.URLError, OSError, ValueError) as e:
            raise TelegramError(f"{method}: network error ({type(e).__name__})") from None
        if not data.get("ok"):
            ra = (data.get("parameters") or {}).get("retry_after") or 0
            raise TelegramError(f"{method}: {data.get('description', 'error')}", ra)
        return data["result"]


# ============================== 7. UI (banner + quote cards + coloured buttons) ==============================
URL_RE = re.compile(r'https?://[^\s<>"\']+')
RANGE_RE = re.compile(r"(?<!\d)(\d+)\s*[-–—]\s*(\d*)(?!\d)")
SESSION_TTL = 1800  # link bhejne ke baad range chunne ke liye 30 min
STATS_FILE = Path(__file__).resolve().with_name("epub_stats.json") if "__file__" in globals() else Path("epub_stats.json")
_stats_lock = threading.Lock()


def hx(s):
    return html.escape(str(s), quote=False)


def cut(s, n):
    s = str(s)
    return s if len(s) <= n else s[:n - 1] + "…"


def _fmt(sec):
    sec = int(max(sec, 0))
    return f"{sec // 60}:{sec % 60:02d}"


def bar(done, total, width=12):
    frac = 0.0 if total <= 0 else min(done / total, 1.0)
    f = int(round(frac * width))
    return "▰" * f + "▱" * (width - f), int(frac * 100)


def stats_get():
    try:
        return json.loads(STATS_FILE.read_text("utf-8"))
    except Exception:  # noqa: BLE001
        return {}


def stats_add(uid):
    with _stats_lock:
        d = stats_get()
        d[str(uid)] = d.get(str(uid), 0) + 1
        try:
            STATS_FILE.write_text(json.dumps(d), "utf-8")
        except OSError:
            pass


PREFS_FILE = STATS_FILE.with_name("epub_prefs.json")
PRESETS = (("r1", 1, 20), ("r2", 20, 100), ("r3", 1, 100))  # (key, first, last) - yahan badal sakte ho


def prefs_get(uid):
    try:
        return json.loads(PREFS_FILE.read_text("utf-8")).get(str(uid)) or {}
    except Exception:  # noqa: BLE001
        return {}


def prefs_save(uid, pref):
    with _stats_lock:
        try:
            d = json.loads(PREFS_FILE.read_text("utf-8"))
        except Exception:  # noqa: BLE001
            d = {}
        d[str(uid)] = pref
        try:
            PREFS_FILE.write_text(json.dumps(d), "utf-8")
        except OSError:
            pass


SEP = "─" * 18


def card(title, sub=None, rows=(), quote=(), foot=None):
    """Header (bold + italic) -> line -> text -> quote box -> bold footer. Sab text yahin escape hota hai."""
    out = [f"<b>{hx(title)}</b>"]
    if sub:
        out.append(f"<i>{hx(sub)}</i>")
    out.append(SEP)
    if rows:
        out.append("\n".join(hx(r) for r in rows))
    if quote:
        out.append("<blockquote>" + "\n".join(hx(q) for q in quote) + "</blockquote>")
    if foot:
        out.append(f"<b>{hx(foot)}</b>")
    return "\n".join(out)


def btn(text, data, style=None):
    """style: 'primary' (neela), 'success' (hara), 'danger' (laal). Purane Telegram app me normal dikhta hai."""
    b = {"text": text, "callback_data": data}
    if style:
        b["style"] = style
    return b


def kb(*rows):
    return {"inline_keyboard": [list(r) for r in rows if r]}


def menu_kb():
    rows = [[btn("📖 How to use", "m:help", "primary")],
            [btn("📋 My Jobs", "m:jobs", "success"), btn("📊 Status", "m:status", "primary")],
            [btn("🛑 Cancel all", "ca", "danger")]]
    if SUPPORT_URL:
        rows[-1].append({"text": "💬 Contact support", "url": SUPPORT_URL})
    return kb(*rows)


def nav_kb(*top):
    """Har screen ke neeche: Back (menu par) aur Close (message hata do)."""
    return kb(*top, [btn("⬅ Back", "m:menu"), btn("✖ Close", "m:close", "danger")])


HELP_CARD = card("📖 How to use", "Novel → EPUB in 3 steps", [
    "1️⃣ Novel ka link bhejo",
    "2️⃣ Total chapters dikhenge, range chuno",
    "3️⃣ EPUB ready hote hi usi message me mil jayegi",
], [
    "⚡ Shortcut · link ke baad range likho",
    "https://site.com/novel/x 5-50",
    "📚 Kai EPUB · kai links ek saath bhejo",
], "/jobs · /cancel · /myid")


class Session:
    """Link scan ho gaya, user ke range chunne ka intezaar."""
    __slots__ = ("sid", "chat", "url", "info", "refs", "dom", "mid", "t", "uid", "sel", "custom")

    def __init__(self, sid, chat, url):
        self.sid, self.chat, self.url = sid, chat, url
        self.info, self.refs, self.dom, self.mid = None, [], None, None
        self.t = time.monotonic()
        self.uid, self.sel, self.custom = 0, "all", None


class Job:
    __slots__ = ("jid", "chat", "uid", "url", "first", "last", "cancel", "mid", "name", "title", "done", "total")

    def __init__(self, jid, chat, uid, url, first, last, mid, title):
        self.jid, self.chat, self.uid, self.url, self.first, self.last = jid, chat, uid, url, first, last
        self.cancel = threading.Event()
        self.mid, self.title = mid, title
        self.name = _host_key(url)
        self.done, self.total = 0, 0

    def rng(self):
        return f"{self.first}–{self.last or 'end'}"


def job_kb(job):
    return kb([btn("✖ Cancel job", f"j:{job.jid}", "danger")])


def parse_range(text, total):
    """'1-20', '55-60', '5-' ya sirf '7' -> (first, last) ya (None, error)."""
    m = RANGE_RE.search(text)
    if m:
        first, last = int(m.group(1)), int(m.group(2) or 0)
    else:
        m = re.fullmatch(r"\s*(\d+)\s*", text)
        if not m:
            return None, "Aise likho: 1-20 ya 55-60"
        first = last = int(m.group(1))
    if first < 1:
        return None, "Chapter number 1 se shuru hota hai"
    if last and last < first:
        return None, f"Range galat hai ({first}-{last})"
    if total:
        if first > total:
            return None, f"Novel me sirf {total} chapters hain"
        last = min(last or total, total)
    return (first, last), None


class Bot:
    def __init__(self, api, allowed=None):
        self.api = api
        self.allowed = set(allowed or ())
        self.jobs = {}  # jid -> Job
        self.sessions = {}  # sid -> Session
        self.awaiting = {}  # chat -> sid (custom range likhne ka intezaar)
        self.next_id = 1
        self.next_sid = 1
        self.lock = threading.Lock()
        self._last_edit = {}  # (chat, message_id) -> time
        self._banner_id = None  # Telegram file_id (pehli baar bhejne ke baad cache)
        self._photos = set()  # (chat, message_id) jo photo+caption wale hain

    # ---- chhote helpers
    def say(self, chat, text, markup=None):
        p = {"chat_id": chat, "text": text[:4000], "parse_mode": "HTML", "disable_web_page_preview": True}
        if markup:
            p["reply_markup"] = markup
        try:
            return self.api.call("sendMessage", p, timeout=15)["message_id"]
        except TelegramError as e:
            print("sendMessage failed:", e, file=sys.stderr)
            return None

    def send_photo(self, chat, text, markup=None):
        """Banner photo + caption. Ye message baad me edit hoke progress aur phir EPUB file ban jata hai."""
        p = {"chat_id": chat, "caption": text[:1000], "parse_mode": "HTML"}
        try:
            if self._banner_id:
                if markup:
                    p["reply_markup"] = markup
                r = self.api.call("sendPhoto", dict(p, photo=self._banner_id), timeout=30)
            elif BANNER.startswith(("http://", "https://")):
                if markup:
                    p["reply_markup"] = markup
                r = self.api.call("sendPhoto", dict(p, photo=BANNER), timeout=30)
            else:
                if BANNER and os.path.isfile(BANNER):
                    data, fname = Path(BANNER).read_bytes(), os.path.basename(BANNER)
                else:
                    data, fname = make_banner_png(), "banner.png"
                if markup:
                    p["reply_markup"] = json.dumps(markup)
                mime = "image/png" if fname.lower().endswith(".png") else "image/jpeg"
                r = self.api.call("sendPhoto", p, files={"photo": (fname, data, mime)}, timeout=60)
            self._banner_id = r["photo"][-1]["file_id"]
            self._photos.add((chat, r["message_id"]))
            return r["message_id"]
        except (TelegramError, OSError, KeyError) as e:
            print("photo failed (text bhej raha hoon):", e, file=sys.stderr)
            return None

    def edit(self, chat, mid, text, markup=None, throttle=True):
        if mid is None:
            return
        key = (chat, mid)
        now = time.monotonic()
        if throttle and now - self._last_edit.get(key, 0) < 3.0:
            return
        self._last_edit[key] = now
        p = {"chat_id": chat, "message_id": mid, "parse_mode": "HTML"}
        if markup is not None:
            p["reply_markup"] = markup  # markup na do to buttons hat jate hain
        try:
            if key in self._photos:
                self.api.call("editMessageCaption", dict(p, caption=text[:1000]), timeout=15)
            else:
                self.api.call("editMessageText", dict(p, text=text[:4000], disable_web_page_preview=True), timeout=15)
        except TelegramError as e:
            if "no text" in str(e).lower():  # photo wala message (bot restart ke baad): caption edit karo
                self._photos.add(key)
                try:
                    self.api.call("editMessageCaption", dict(p, caption=text[:1000]), timeout=15)
                except TelegramError:
                    pass

    def answer(self, cq_id, text="", alert=False):
        try:
            self.api.call("answerCallbackQuery", {"callback_query_id": cq_id, "text": text[:190],
                                                  "show_alert": alert}, timeout=10)
        except TelegramError:
            pass

    def stop(self):
        for j in list(self.jobs.values()):
            j.cancel.set()

    def denied(self, chat, uid):
        self.say(chat, card("🔒 Access denied", "Private bot", ["Aapko is bot ki permission nahi hai."],
                            [f"🆔 Your ID · {uid}"]))

    # ---- screens
    def welcome_text(self, name, uid):
        done = stats_get().get(str(uid), 0)
        return "\n".join([
            f"👋 <b>Hi {hx(cut(name, 24))}!</b> ✨",
            "📚 <i>Novel → EPUB converter</i>",
            SEP,
            "🔁 Main novel ke link se <b>EPUB</b> bana deta hoon — aap <b>chapter range</b> chun sakte ho, "
            "formatting aur chapter list <b>bilkul waisi hi</b> rehti hai.",
            "<blockquote>" + "\n".join([
                f"📖 Converted · {done} EPUBs",
                f"⚙️ Running · {len(self.jobs)} jobs",
                f"🚀 Speed · {WORKERS} chapters parallel",
            ]) + "</blockquote>",
            "🔗 <b>Novel ka link bhejo</b> — ya neeche se option chuno 👇",
        ])

    def welcome(self, chat, name="Friend", uid=0):
        """Naya /start message (banner ke saath). Baaki sab screens isi message me edit hoti hain."""
        text, markup = self.welcome_text(name, uid), menu_kb()
        if self.send_photo(chat, text, markup) is None:
            self.say(chat, text, markup)

    def status_view(self, chat, uid):
        mine = sum(1 for j in self.jobs.values() if j.chat == chat)
        text = card("📊 Status", "Bot ki halat", quote=[
            f"🆔 Your ID · {uid}",
            f"⚙️ Your jobs · {mine}",
            f"🌍 Total jobs · {len(self.jobs)}/{MAX_JOBS_TOTAL}",
            f"📖 Converted · {stats_get().get(str(uid), 0)} EPUBs",
            f"🕒 Updated · {datetime.now().strftime('%H:%M:%S')}",
        ])
        return text, nav_kb([btn("🔄 Refresh", "m:status", "primary")])

    def jobs_view(self, chat):
        mine = [j for j in list(self.jobs.values()) if j.chat == chat]
        stamp = f"🕒 Updated · {datetime.now().strftime('%H:%M:%S')}"
        refresh = [btn("🔄 Refresh", "m:jobs", "primary")]
        if not mine:
            return card("📋 My Jobs", "Abhi khali hai", ["Koi kaam nahi chal raha."], [stamp],
                        "Novel ka link bhejo 👇"), nav_kb(refresh)
        q = []
        for j in mine:
            _, pct = bar(j.done, j.total)
            q.append(f"#{j.jid} · {cut(j.title, 26)}")
            q.append(f"     {j.rng()} · {pct}% · {cut(j.name, 16)}")
        q.append(stamp)
        rows = [[btn(f"✖ Cancel #{j.jid}", f"j:{j.jid}", "danger") for j in mine[:3]]]
        if len(mine) > 1:
            rows.append([btn("🛑 Cancel all", "ca", "danger")])
        rows.append(refresh)
        return card("📋 My Jobs", f"{len(mine)} running", quote=q), nav_kb(*rows)

    # ---- link scan -> info card
    def new_session(self, chat, url):
        now = time.monotonic()
        with self.lock:
            for s in [s for s in self.sessions.values() if now - s.t > SESSION_TTL]:
                self.sessions.pop(s.sid, None)
            sess = Session(self.next_sid, chat, url)
            self.next_sid += 1
            self.sessions[sess.sid] = sess
        text = card("🔍 Scanning…", "Chapter list dhoondh raha hoon", [cut(url, 60)])
        markup = kb([btn("✖ Cancel", f"x:{sess.sid}", "danger")])
        sess.mid = self.send_photo(chat, text, markup)
        if sess.mid is None:
            sess.mid = self.say(chat, text, markup)
        return sess

    def scan(self, sess, preset, uid):
        chat = sess.chat
        try:
            check_public(sess.url)
            dom = get_dom(sess.url)
            info = book_info(dom, sess.url)
            refs = find_toc(dom, sess.url)
        except (FetchError, ParseError) as e:
            self.drop_session(sess)
            self.edit(chat, sess.mid, card("❌ Failed", "Link scan nahi hua", [cut(str(e), 80)], foot="Sahi link bhejo"),
                      kb(), throttle=False)
            return
        except Exception:  # noqa: BLE001
            traceback.print_exc()
            self.drop_session(sess)
            self.edit(chat, sess.mid, card("❌ Error", "Internal error", ["Thodi der baad try karo."]), kb(),
                      throttle=False)
            return
        if self.sessions.get(sess.sid) is not sess:
            return  # user ne scan ke dauran cancel kar diya
        sess.info, sess.refs, sess.dom = info, refs, dom
        sess.uid = uid
        pref = prefs_get(uid)  # "Save as default" wali choice
        if pref.get("sel") == "cust" and len(pref.get("range") or ()) == 2:
            sess.sel, sess.custom = "cust", tuple(pref["range"])
        elif pref.get("sel"):
            sess.sel = pref["sel"]
        if preset:
            err = self.start_job(sess, uid, *preset)
            if err:
                self.drop_session(sess)
                self.edit(chat, sess.mid, card("⚠️ Ruko", None, [err]), kb(), throttle=False)
            return
        self.show_choice(sess)

    def drop_session(self, sess):
        with self.lock:
            self.sessions.pop(sess.sid, None)
            if self.awaiting.get(sess.chat) == sess.sid:
                self.awaiting.pop(sess.chat, None)

    def visible_presets(self, sess):
        total = len(sess.refs)
        return [(k, a, b) for k, a, b in PRESETS
                if not total or (a <= total and not (a == 1 and b >= total))]

    def sel_range(self, sess):
        total = len(sess.refs)
        if sess.sel == "cust" and sess.custom:
            return sess.custom
        for k, a, b in PRESETS:
            if sess.sel == k:
                return a, (min(b, total) if total else b)
        return 1, (min(total, MAX_CHAPTERS) if total else 0)

    def show_choice(self, sess):
        total, info, sid = len(sess.refs), sess.info, sess.sid
        vis = self.visible_presets(sess)
        if sess.sel == "cust" and not sess.custom or sess.sel not in ("all", "cust", *[k for k, _, _ in vis]):
            sess.sel = "all"
        first, last = self.sel_range(sess)

        def opt(key, label):
            on = sess.sel == key
            return btn(("◉ " if on else "") + label, f"p:{sid}:{key}", "success" if on else None)

        def span(a, b):
            return f"{a}–{b}" if b else f"{a}–end"

        row1 = [opt("all", "📚 Full novel" if total else "📚 All (slow)")]
        row1 += [opt(k, span(a, min(b, total) if total else b)) for k, a, b in vis[:2]]
        row2 = [opt(k, span(a, min(b, total) if total else b)) for k, a, b in vis[2:]]
        row2.append(btn(f"◉ ✏️ {span(first, last)}", f"p:{sid}:c", "success") if sess.sel == "cust"
                    else btn("✏️ Custom…", f"p:{sid}:c"))
        if total:
            quote = [f"📚 Chapters · {total}", f"✍️ Author · {cut(info['author'], 24)}",
                     f"🌐 Source · {cut(_host_key(sess.url), 24)}"]
            n = last - first + 1
            pick = "Full novel" if (first, last) == (1, min(total, MAX_CHAPTERS)) else span(first, last)
            quote.append(f"🎯 Selected · {pick} ({n} chapters)")
        else:
            quote = ["⚠️ Chapter list nahi mili", "🐢 Next-link mode (slow)",
                     f"🌐 Source · {cut(_host_key(sess.url), 24)}", f"🎯 Selected · {span(first, last)}"]
        foot = f"Max {MAX_CHAPTERS} chapters ek EPUB me" if total > MAX_CHAPTERS else "Create EPUB Book dabao 👇"
        self.edit(sess.chat, sess.mid, card(f"📖 {cut(info['title'], 40)}", "Range chuno, phir Create dabao",
                                            quote=quote, foot=foot),
                  kb(row1, row2, [btn("📖 Create EPUB Book", f"p:{sid}:go", "success")],
                     [btn("💾 Save as default", f"p:{sid}:sv", "primary"), btn("✖ Cancel", f"x:{sid}", "danger")]),
                  throttle=False)

    # ---- job start (limits check + thread)
    def start_job(self, sess, uid, first, last):
        chat = sess.chat
        with self.lock:
            if len(self.jobs) >= MAX_JOBS_TOTAL:
                return "Bot par abhi bahut kaam hai, thodi der baad try karo."
            if sum(1 for j in self.jobs.values() if j.chat == chat) >= MAX_JOBS_PER_CHAT:
                return f"Ek saath max {MAX_JOBS_PER_CHAT} kaam chal sakte hain."
            job = Job(self.next_id, chat, uid, sess.url, first, last, sess.mid, sess.info["title"])
            self.next_id += 1
            self.jobs[job.jid] = job
            self.sessions.pop(sess.sid, None)
            self.awaiting.pop(chat, None)
        job.total = (last - first + 1) if last else max(len(sess.refs) - first + 1, 0)
        self.progress(job, "Shuru ho raha hai", throttle=False)
        threading.Thread(target=self.job, args=(job, sess), daemon=True).start()
        return None

    def progress(self, job, phase, done=0, total=0, rate=0.0, eta="--", throttle=True):
        job.done, job.total = done, total or job.total
        b, pct = bar(done, job.total)
        q = [f"{b} {pct}%", f"📥 Done · {done}/{job.total}", f"📑 Range · {job.rng()}"]
        if rate:
            q.append(f"⚡ {rate:.1f} ch/s · ⏳ ETA {eta}")
        self.edit(job.chat, job.mid, card(f"📖 {cut(job.title, 40)}", f"Job #{job.jid} · {cut(job.name, 22)}",
                                          [f"⚙️ {phase}"], q), job_kb(job), throttle=throttle)

    def finish(self, job, head, sub, rows=(), quote=(), foot=None):
        self.edit(job.chat, job.mid, card(head, sub, rows, quote, foot), kb([btn("🏠 Menu", "m:menu", "primary")]),
                  throttle=False)

    def deliver(self, job, cap, fname, data):
        """EPUB usi progress message ki jagah aa jati hai (editMessageMedia). Na ho paye to naya document bhejo.
        True = usi message me gayi."""
        chat, mid = job.chat, job.mid
        if mid is not None and (chat, mid) in self._photos:
            media = {"type": "document", "media": "attach://book", "caption": cap[:1000], "parse_mode": "HTML"}
            try:
                self.api.call("editMessageMedia", {"chat_id": chat, "message_id": mid, "media": json.dumps(media)},
                              files={"book": (fname, data, "application/epub+zip")}, timeout=300)
                self._photos.discard((chat, mid))
                return True
            except TelegramError as e:
                print("editMessageMedia failed (naya document bhej raha hoon):", e, file=sys.stderr)
        self.api.call("sendDocument", {"chat_id": chat, "caption": cap, "parse_mode": "HTML"},
                      files={"document": (fname, data, "application/epub+zip")}, timeout=300)
        return False

    # ---- messages
    def handle(self, upd):
        if "callback_query" in upd:
            self.on_callback(upd["callback_query"])
            return
        msg = upd.get("message")
        if not msg or "chat" not in msg:
            return
        chat, frm = msg["chat"]["id"], (msg.get("from") or {})
        uid, name = frm.get("id", 0), frm.get("first_name") or "Friend"
        text = (msg.get("text") or "").strip()
        if not text:
            return
        parts = text.split()
        cmd = parts[0].split("@")[0].lower()
        if cmd == "/myid":
            self.say(chat, card("🆔 Your ID", None, quote=[str(uid)]))
            return
        if self.allowed and uid not in self.allowed:
            self.denied(chat, uid)
            return
        if cmd in ("/start", "/menu"):
            self.welcome(chat, name, uid)
            return
        if cmd == "/help":
            self.say(chat, HELP_CARD, nav_kb())
            return
        if cmd == "/status":
            self.say(chat, *self.status_view(chat, uid))
            return
        if cmd == "/jobs":
            self.say(chat, *self.jobs_view(chat))
            return
        if cmd == "/cancel":
            arg = parts[1].lstrip("#") if len(parts) > 1 else ""
            mine = [j for j in list(self.jobs.values()) if j.chat == chat]
            if arg.isdigit():
                mine = [j for j in mine if j.jid == int(arg)]
            if not mine:
                self.say(chat, card("ℹ️ Info", None, ["Aisa koi kaam nahi chal raha."]))
                return
            for j in mine:
                j.cancel.set()
            self.say(chat, card("🛑 Cancelling", None, quote=[", ".join(f"#{j.jid}" for j in mine)]))
            return

        matches = list(URL_RE.finditer(text))
        # custom range ka intezaar chal raha ho to ye text range hai
        if not matches and chat in self.awaiting:
            sess = self.sessions.get(self.awaiting[chat])
            if sess is None or sess.info is None:
                self.awaiting.pop(chat, None)
            else:
                rng, err = parse_range(text, len(sess.refs))
                if err:
                    self.say(chat, card("⚠️ Range galat hai", None, [err], foot="Example · 1-20"))
                    return
                sess.sel, sess.custom = "cust", rng
                self.awaiting.pop(chat, None)
                self.show_choice(sess)
                return
        if not matches:
            self.say(chat, card("🔗 Link chahiye", "Novel ka http/https link bhejo", foot="/help dekho"), menu_kb())
            return
        for i, m in enumerate(matches):
            url = m.group(0)
            end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
            r = RANGE_RE.search(text[m.end():end])  # sirf is link ke baad wala hissa
            preset = None
            if r:
                first, last = max(int(r.group(1)), 1), int(r.group(2) or 0)
                if last and last < first:
                    self.say(chat, card("⚠️ Range galat hai", None, [f"{first}-{last}", "Ye link chhod diya."]))
                    continue
                preset = (first, last)
            sess = self.new_session(chat, url)
            threading.Thread(target=self.scan, args=(sess, preset, uid), daemon=True).start()

    # ---- button presses
    def on_callback(self, cq):
        cid, frm = cq["id"], (cq.get("from") or {})
        uid, name = frm.get("id", 0), frm.get("first_name") or "Friend"
        msg = cq.get("message") or {}
        chat, mid = (msg.get("chat") or {}).get("id"), msg.get("message_id")
        data = cq.get("data") or ""
        if chat is None:
            self.answer(cid)
            return
        if self.allowed and uid not in self.allowed:
            self.answer(cid, "Permission nahi hai", True)
            return
        kind, _, rest = data.partition(":")
        if kind == "m":  # menu: isi message me edit hota hai (naya message nahi)
            self.answer(cid)
            if rest == "close":
                try:
                    self.api.call("deleteMessage", {"chat_id": chat, "message_id": mid}, timeout=10)
                except TelegramError:
                    self.edit(chat, mid, card("✖ Closed", None, ["Naya link bhejo ya /start dabao."]), kb(),
                              throttle=False)
                return
            if rest == "status":
                text, markup = self.status_view(chat, uid)
            elif rest == "jobs":
                text, markup = self.jobs_view(chat)
            elif rest == "help":
                text, markup = HELP_CARD, nav_kb()
            else:
                text, markup = self.welcome_text(name, uid), menu_kb()
            self.edit(chat, mid, text, markup, throttle=False)
        elif kind == "j":  # cancel job
            job = self.jobs.get(int(rest)) if rest.isdigit() else None
            if job is None or job.chat != chat:
                self.answer(cid, "Ye kaam pehle hi khatam ho chuka hai")
                return
            job.cancel.set()
            self.answer(cid, f"#{job.jid} cancel ho raha hai...")
        elif kind == "ca":  # cancel all
            mine = [j for j in list(self.jobs.values()) if j.chat == chat]
            for j in mine:
                j.cancel.set()
            self.answer(cid, f"{len(mine)} kaam cancel ho rahe hain" if mine else "Koi kaam nahi chal raha")
        elif kind == "x":  # cancel session
            sess = self.sessions.get(int(rest)) if rest.isdigit() else None
            self.answer(cid, "Cancel ho gaya")
            if sess is not None and sess.chat == chat:
                self.drop_session(sess)
                self.edit(chat, sess.mid, card("🚫 Cancelled", None, ["Naya link bhej sakte ho."]),
                          kb([btn("🏠 Menu", "m:menu", "primary")]), throttle=False)
        elif kind == "p":  # range pick
            sid, _, choice = rest.partition(":")
            sess = self.sessions.get(int(sid)) if sid.isdigit() else None
            if sess is None or sess.chat != chat or sess.info is None:
                self.answer(cid, "Ye session purana ho gaya. Link dobara bhejo.", True)
                return
            sess.t = time.monotonic()
            total = len(sess.refs)
            if choice == "c":
                with self.lock:
                    self.awaiting[chat] = sess.sid
                self.answer(cid)
                q = ["1-20", "55-60", "100-  (100 se aakhir tak)"]
                self.edit(chat, sess.mid, card("✍️ Custom Range", "Range likh ke bhejo",
                                               [f"Total chapters · {total}"] if total else (), q,
                                               "Example · 55-60"),
                          kb([btn("⬅ Back", f"p:{sess.sid}:b")]), throttle=False)
            elif choice == "b":
                with self.lock:
                    self.awaiting.pop(chat, None)
                self.answer(cid)
                self.show_choice(sess)
            elif choice == "go":
                err = self.start_job(sess, uid, *self.sel_range(sess))
                self.answer(cid, err or "Shuru ho gaya ✅", bool(err))
            elif choice == "sv":
                pref = {"sel": sess.sel}
                if sess.sel == "cust" and sess.custom:
                    pref["range"] = list(sess.custom)
                prefs_save(uid, pref)
                self.answer(cid, "💾 Default save ho gaya")
            elif choice == "all" or choice in [k for k, _, _ in PRESETS]:
                sess.sel = choice
                with self.lock:
                    self.awaiting.pop(chat, None)
                self.answer(cid)
                self.show_choice(sess)
            else:
                self.answer(cid)
        else:
            self.answer(cid)

    # ---- ek novel ka poora kaam
    def job(self, job, sess):
        chat, url, first, last, cancel = job.chat, job.url, job.first, job.last, job.cancel
        tmp = Path(tempfile.mkdtemp(prefix="epub"))
        try:
            info, refs, dom = dict(sess.info), sess.refs, sess.dom
            sess.dom = None
            if refs:
                full_n = len(refs)
                refs = refs[first - 1:(last or len(refs))][:MAX_CHAPTERS]
                if not refs:
                    raise ParseError("Is range me koi chapter nahi hai")
                info["label"] = range_label(refs, url, first, full_n)
                job.last = first + len(refs) - 1
                chapters = self._download_all(refs, job)
            else:
                chapters = self._crawl(dom, url, first, last, job)
            if not chapters:
                raise ParseError("Koi chapter nahi mila. Chapter ya novel ka sahi link bhejo.")
            label = info.get("label") or f"[ {first}-{first + len(chapters) - 1} ]"
            book_title = f"{label} {ascii_clean(info['title']) or info['title']}"
            info["title"] = book_title
            self.progress(job, "EPUB ban rahi hai", len(chapters), len(chapters), throttle=False)
            out = pack_epub(info, chapters, tmp / "book.epub")
            size = out.stat().st_size
            if size > TG_LIMIT:
                raise ParseError("EPUB 50 MB se badi hai. Chhoti range chuno, jaise 1-500")
            bad = [c for c in chapters if not c.ok]
            summary = [f"📚 Chapters · {len(chapters)}" + (f" ({len(bad)} fail)" if bad else ""),
                       f"💾 Size · {size / 1048576:.1f} MB"]
            cap = card(f"📚 {cut(book_title, 60)}", f"Job #{job.jid}", quote=summary, foot="Happy reading 📖")
            self.progress(job, "Telegram par bhej raha hoon", len(chapters), len(chapters), throttle=False)
            fname = tg_filename(safe_filename(book_title, 120)) + ".epub"
            in_place = self.deliver(job, cap, fname, out.read_bytes())
            stats_add(job.uid)
            if not in_place:  # file naye message me gayi, progress message ko "Completed" dikhao
                self.finish(job, "✅ Completed", f"Job #{job.jid}", [f"📖 {cut(info['title'], 50)}"], summary,
                            "EPUB upar bhej di gayi")
            if bad:
                self.say(chat, card(f"⚠️ #{job.jid} · {len(bad)} chapters fail", "Site se nahi aaye",
                                    quote=[cut(c.title, 40) for c in bad[:20]], foot="Wahi range dobara bhejo"))
        except Cancelled:
            self.finish(job, "🚫 Cancelled", f"Job #{job.jid}", ["Kaam rok diya gaya."])
        except (FetchError, ParseError) as e:
            self.finish(job, "❌ Failed", f"Job #{job.jid}", [cut(str(e), 90)])
        except TelegramError as e:
            print("send failed:", e, file=sys.stderr)
            self.finish(job, "❌ Send failed", f"Job #{job.jid}", ["Telegram par file nahi gayi.", "Dobara try karo."])
        except Exception:  # noqa: BLE001
            traceback.print_exc()
            self.finish(job, "❌ Error", f"Job #{job.jid}", ["Internal error.", "Thodi der baad try karo."])
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
            self._last_edit.pop((chat, job.mid), None)
            with self.lock:
                self.jobs.pop(job.jid, None)

    def _run_batch(self, refs, idxs, results, tries, phase, job):
        """Daemon worker threads queue se chapters uthate hain."""
        q = queue.Queue()
        for i in idxs:
            q.put(i)
        total, done, lk, t0 = q.qsize(), [0], threading.Lock(), time.monotonic()
        cancel = job.cancel

        def worker():
            while not cancel.is_set():
                try:
                    i = q.get_nowait()
                except queue.Empty:
                    return
                try:
                    results[i] = fetch_chapter(refs[i], tries, cancel)
                except Exception as e:  # noqa: BLE001
                    results[i] = _failed(refs[i].title, e)
                with lk:
                    done[0] += 1

        threads = [threading.Thread(target=worker, daemon=True) for _ in range(min(WORKERS, total))]
        for t in threads:
            t.start()
        while any(t.is_alive() for t in threads):
            d, el = done[0], time.monotonic() - t0
            rate = d / el if el > 1 else 0.0
            self.progress(job, phase, d, total, rate, _fmt((total - d) / rate) if rate > 0 else "--")
            time.sleep(1)

    def _download_all(self, refs, job):
        n = len(refs)
        results = [None] * n
        lim = get_limiter(refs[0].url)
        job.total = n
        self._run_batch(refs, range(n), results, CH_TRIES, "Downloading", job)
        for p in range(1, REPAIR_PASSES + 1):  # fail wale chapters ko dheere dobara try karo
            if job.cancel.is_set():
                break
            bad = [i for i, c in enumerate(results) if c is None or not c.ok]
            if not bad:
                break
            lim.cap(max(MIN_WORKERS, WORKERS * 3 // 4))
            self.progress(job, f"{len(bad)} fail, retry {p}/{REPAIR_PASSES}", n - len(bad), n, throttle=False)
            time.sleep(1 * p)
            self._run_batch(refs, bad, results, CH_TRIES + 1, f"Retry round {p}", job)
        if job.cancel.is_set():
            raise Cancelled()
        return [c or _failed(refs[i].title, "pata nahi kyun") for i, c in enumerate(results)]

    def _crawl(self, dom, url, first, last, job):
        """Chapter list na mile to 'Next' link follow karo (ek-ek karke)."""
        cur = url
        if not find_next(dom, url):
            ff = find_first_chapter(dom, url)
            if ff:
                cur, dom = ff, None
        chapters, seen, idx = [], set(), 0
        limit = min(last or MAX_CHAPTERS, first + MAX_CHAPTERS - 1)
        job.total = max(limit - first + 1, 1)
        while cur and cur not in seen and idx < limit:
            if job.cancel.is_set():
                raise Cancelled()
            seen.add(cur)
            try:
                d = dom if dom is not None else get_dom(cur)
            except FetchError:
                if chapters:
                    break
                raise
            dom = None
            idx += 1
            if idx >= first:
                chapters.append(make_chapter(page_title(d) or f"Chapter {idx}", d))
                self.progress(job, "Downloading (slow mode)", len(chapters), job.total)
            cur = find_next(d, cur)
        return chapters

    # ---- main loop
    def run(self):
        me = self.api.call("getMe")
        try:
            self.api.call("deleteWebhook")
        except TelegramError:
            pass
        try:
            self.api.call("setMyCommands", {"commands": [
                {"command": "start", "description": "Bot shuru karo"},
                {"command": "help", "description": "Guide dekho"},
                {"command": "jobs", "description": "Chalte kaam dekho"},
                {"command": "status", "description": "Bot status"},
                {"command": "cancel", "description": "Kaam rok do"},
                {"command": "myid", "description": "Apna Telegram ID"}]})
        except TelegramError:
            pass
        offset = None
        try:  # purane pending messages skip karo
            old = self.api.call("getUpdates", {"offset": -1, "timeout": 0})
            if old:
                offset = old[-1]["update_id"] + 1
        except TelegramError:
            pass
        print(f"Bot @{me.get('username')} chal raha hai. Workers/job: {WORKERS}, max jobs: {MAX_JOBS_TOTAL}. "
              f"Allowed: {sorted(self.allowed) or 'sab log'}", flush=True)
        print("Telegram me bot kholo aur /start bhejo. Rokne ke liye Stop dabao.", flush=True)
        backoff = 1
        while True:
            params = {"timeout": 25, "allowed_updates": ["message", "callback_query"]}
            if offset is not None:
                params["offset"] = offset
            try:
                updates = self.api.call("getUpdates", params, timeout=35)
                backoff = 1
            except TelegramError as e:
                wait = e.retry_after or backoff
                print("getUpdates:", e, f"(wait {wait}s)", file=sys.stderr, flush=True)
                time.sleep(wait)
                backoff = min(backoff * 2, 15)
                continue
            for u in updates if isinstance(updates, list) else []:
                offset = u["update_id"] + 1
                try:
                    self.handle(u)
                except Exception:  # noqa: BLE001
                    traceback.print_exc()


# ============================== 8. RENDER FREE: health server + keep-alive ==============================
class _Health(BaseHTTPRequestHandler):
    def _ok(self, body=True):
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.send_header("Content-Length", "2")
        self.end_headers()
        if body:
            self.wfile.write(b"ok")

    def do_GET(self):
        self._ok()

    def do_HEAD(self):
        self._ok(False)

    def log_message(self, *a):
        pass


def _keepalive(url):
    """Render free 15 min bina traffic ke so jata hai. Har 10 min apne aap ko ping karo."""
    while True:
        time.sleep(600)
        try:
            request.urlopen(url, timeout=20).read()
        except Exception:  # noqa: BLE001
            pass


def start_web():
    port = os.environ.get("PORT")
    if not port:
        return
    srv = ThreadingHTTPServer(("0.0.0.0", int(port)), _Health)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    url = os.environ.get("RENDER_EXTERNAL_URL")
    if url:
        threading.Thread(target=_keepalive, args=(url,), daemon=True).start()
    print(f"Health server port {port} par chal raha hai.", flush=True)


def main():
    start_web()
    token = (os.environ.get("TELEGRAM_BOT_TOKEN") or BOT_TOKEN).strip()
    if not re.fullmatch(r"\d{5,}:[A-Za-z0-9_-]{10,}", token):
        print("Bot token galat/khali hai. Render > Environment me TELEGRAM_BOT_TOKEN daalo.", file=sys.stderr)
        return 2
    allowed = set(ALLOWED_USERS) | {int(x) for x in re.findall(r"\d+", os.environ.get("ALLOWED_USERS", ""))}
    if not allowed:
        print("WARNING: ALLOWED_USERS khali hai - koi bhi bot use kar sakta hai.", file=sys.stderr)
    bot = Bot(TelegramAPI(token), allowed)
    try:
        bot.run()
    except KeyboardInterrupt:
        print("\nStopped.")
        bot.stop()
    except TelegramError as e:
        print(f"Start nahi hua: {e} (token aur internet check karo)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    main()
