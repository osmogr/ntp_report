#!/usr/bin/env python3
"""
ntp_report.py - Poll a list of NTP sources with "ntpdate -q" and build an
email report (plain text + HTML) with aligned columns and a combined offset.

Works with both ntpdate implementations shipped by Ubuntu:

  NTP Classic ntpdate 4.2.8   (Ubuntu 22.04 and earlier)
    server 192.0.2.10, stratum 2, offset +0.001234, delay 0.02563

  NTPsec ntpdate wrapper      (Ubuntu 24.04 and later; runs ntpdig)
    2026-11-23 15:15:00.123456 (-0800) +0.001234 +/- 0.012345 host 192.0.2.10 s2 no-leap

Each source is queried by its own ntpdate process (in parallel), so every
source gets exactly one row no matter which implementation is installed.

Examples:
  ntp_report.py time.google.com time.cloudflare.com 10.10.1.5
  ntp_report.py -f /etc/ntp_report/sources.txt
  ntp_report.py -f sources.txt --to noc@example.com --smtp mail.example.com
  ntp_report.py -f sources.txt --to noc@example.com --sendmail --mail-on warn

Sources file: one hostname or IP per line. Blank lines and "#" comments are
ignored, as is anything after the first word on a line.

SMTP password (if --smtp-user is used) is read from NTP_REPORT_SMTP_PASSWORD.

Exit status (Nagios style): 0 = OK, 1 = WARN, 2 = CRIT, 3 = UNKNOWN
Requires Python 3.8+ and the standard library only.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import html
import os
import re
import shutil
import smtplib
import socket
import ssl
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from email.message import EmailMessage
from email.utils import formatdate, make_msgid
from typing import Dict, List, Optional, Sequence, Tuple

# ---------------------------------------------------------------------------
# Defaults (edit to taste, or override on the command line)
# ---------------------------------------------------------------------------

# Used only when no sources are given on the command line or with -f.
DEFAULT_SOURCES = [
    "time.google.com",
    "time.cloudflare.com",
    "time.nist.gov",
    "ntp.ubuntu.com",
]

DEFAULT_WARN_MS = 100.0     # |offset| at or above this is WARN
DEFAULT_CRIT_MS = 1000.0    # |offset| at or above this is CRIT

STATUS_RANK = {"OK": 0, "WARN": 1, "CRIT": 2, "UNKNOWN": 3}

# cron runs with PATH=/usr/bin:/bin, but ntpdate lives in /usr/sbin.
SAFE_PATH = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

MAX_NAME_WIDTH = 40

# ---------------------------------------------------------------------------
# Output parsing
# ---------------------------------------------------------------------------

NUM = r"[-+]?\d+(?:\.\d+)?"

# NTP Classic, one line per server address:
#   server 192.0.2.10, stratum 2, offset -0.000123, delay 0.02579
CLASSIC_LINE = re.compile(
    r"^\s*server\s+(?P<addr>\S+?),\s*stratum\s+(?P<stratum>\d+),\s*"
    r"offset\s+(?P<offset>" + NUM + r"),\s*delay\s+(?P<delay>" + NUM + r")"
)

# NTP Classic, the server it would have chosen:
#   23 Nov 15:15:00 ntpdate[123]: adjust time server 192.0.2.10 offset -0.000123 sec
CLASSIC_PICK = re.compile(
    r"\b(?:adjust|step) time server\s+(?P<addr>\S+)\s+offset\s+(?P<offset>" + NUM + r")"
)

# NTPsec ntpdig (via the ntpdate wrapper), one line for the chosen server:
#   2026-11-23 15:15:00.123456 (-0800) +0.001234 +/- 0.012345 host 192.0.2.10 s2 no-leap
NTPSEC_LINE = re.compile(
    r"\((?P<tz>[-+]\d{4})\)\s+(?P<offset>" + NUM + r")\s+\+/-\s+(?P<err>" + NUM + r")\s+"
    r"(?P<hosts>\S+(?:\s+\S+)?)\s+s(?P<stratum>\d+)\s+(?P<leap>[a-z-]+)\s*$"
)

# NTP Classic prefixes messages with a syslog-style stamp; strip it.
SYSLOG_PREFIX = re.compile(r"^\s*\d{1,2}\s+[A-Za-z]{3}\s+\d{2}:\d{2}:\d{2}\s+ntpdate\[\d+\]:\s*")

DNS_ERRORS = (
    "name or service not known",
    "temporary failure in name resolution",
    "no address associated",
    "can't find host",
    "error resolving",
    "lookup of",
)

# Allowed characters in a source name; also blocks values that look like options.
SOURCE_RE = re.compile(r"^[A-Za-z0-9_.:%-]+$")


@dataclass
class Result:
    source: str
    address: str = "-"
    stratum: Optional[int] = None
    offset: Optional[float] = None   # seconds; positive = this host is behind
    delay: Optional[float] = None    # seconds; classic = round trip, NTPsec = +/- bound
    state: str = "ERROR"             # REPLY, NO REPLY, DNS FAIL, UNSYNC, REJECTED, TIMEOUT, ERROR
    detail: str = ""
    flavor: str = ""                 # "classic" or "ntpsec" (from the output format)
    dev: Optional[float] = None      # offset minus combined offset
    status: str = ""                 # label shown in the report

    @property
    def usable(self) -> bool:
        return self.state == "REPLY" and self.offset is not None


def clean_message(line: str, limit: int = 160) -> str:
    text = SYSLOG_PREFIX.sub("", line).strip()
    return text if len(text) <= limit else text[:limit - 3] + "..."


def classify_failure(res: Result, lines: List[str]) -> Result:
    """Fill in state/detail when no usable sample line was found."""
    lower = [ln.lower() for ln in lines]
    for ln, lo in zip(lines, lower):
        if any(key in lo for key in DNS_ERRORS):
            res.state = "DNS FAIL"
            res.detail = clean_message(ln)
            return res
    for ln, lo in zip(lines, lower):
        # NTPsec: "ntpdig: 192.0.2.1: Response dropped: stratum too high"
        if "response dropped:" in lo:
            reason = ln[lo.index("response dropped:") + len("response dropped:"):].strip()
            unsync = "stratum too high" in lo or "leap not in sync" in lo
            res.state = "UNSYNC" if unsync else "REJECTED"
            res.detail = "server replied but the reply was dropped: %s" % reason
            return res
    if not lines:
        res.state = "ERROR"
        res.detail = "ntpdate produced no output"
    elif any("no eligible servers" in lo for lo in lower):
        res.state = "NO REPLY"
        res.detail = "no response from server"
    elif any("no server suitable" in lo for lo in lower):
        # Classic ntpdate prints only this for both "no answer" and "answered
        # but not synchronized", so say so rather than guess.
        res.state = "NO REPLY"
        res.detail = "no usable reply (server unreachable or not synchronized)"
    else:
        res.state = "ERROR"
        res.detail = clean_message(lines[-1])
    return res


def parse_output(source: str, text: str) -> Result:
    """Turn the output of one 'ntpdate -q <source>' run into a Result."""
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    res = Result(source=source)

    # NTPsec format: a single line for the selected server.
    for ln in lines:
        m = NTPSEC_LINE.search(ln)
        if not m:
            continue
        res.flavor = "ntpsec"
        res.address = m.group("hosts").split()[-1]
        res.stratum = int(m.group("stratum"))
        res.offset = float(m.group("offset"))
        res.delay = float(m.group("err"))
        leap = m.group("leap")
        if leap == "unsync" or not 1 <= res.stratum <= 15:
            res.state = "UNSYNC"
            res.detail = "server is not synchronized (stratum %d, %s)" % (res.stratum, leap)
        else:
            res.state = "REPLY"
        return res

    # NTP Classic format: one line per address, then the one it picked.
    samples = []
    for ln in lines:
        m = CLASSIC_LINE.search(ln)
        if m:
            samples.append((m.group("addr"), int(m.group("stratum")),
                            float(m.group("offset")), float(m.group("delay"))))
    if not samples:
        return classify_failure(res, lines)

    res.flavor = "classic"
    picked = None
    for ln in lines:
        m = CLASSIC_PICK.search(ln)
        if m:
            picked = next((s for s in samples if s[0] == m.group("addr")), None)

    synced = [s for s in samples if 1 <= s[1] <= 15]
    unsynced = [s for s in samples if s[1] >= 16]

    if picked is not None:
        res.state = "REPLY"
        chosen = picked
    elif synced:
        res.state = "REJECTED"
        chosen = min(synced, key=lambda s: s[3])
        res.detail = ("replied (offset %s ms) but ntpdate rejected it as unsuitable"
                      % fmt_ms(chosen[2], signed=True))
    elif unsynced:
        res.state = "UNSYNC"
        chosen = unsynced[0]
        res.detail = "server is not synchronized (stratum %d)" % chosen[1]
    else:
        # Classic reports "stratum 0, offset 0.000000, delay 0.00000" for no answer.
        res.state = "NO REPLY"
        chosen = samples[0]
        res.detail = "no response from server"

    res.address = chosen[0]
    res.stratum = chosen[1] if chosen[1] > 0 else None
    if res.state == "REPLY":
        res.offset = chosen[2]
        res.delay = chosen[3]
    return res


# ---------------------------------------------------------------------------
# Running ntpdate
# ---------------------------------------------------------------------------

def find_ntpdate(explicit: Optional[str]) -> Optional[str]:
    if explicit:
        return explicit if os.path.isfile(explicit) and os.access(explicit, os.X_OK) else None
    return shutil.which("ntpdate", path=SAFE_PATH + os.pathsep + os.environ.get("PATH", ""))


def detect_flavor(path: str) -> str:
    """The NTPsec ntpdate is a small shell script that calls ntpdig."""
    try:
        with open(path, "rb") as fh:
            head = fh.read(65536)
    except OSError:
        return "unknown"
    if head.startswith(b"#!") and b"ntpdig" in head:
        return "ntpsec"
    return "classic"


def query_source(ntpdate: str, source: str, query_timeout: float, max_wait: float) -> Result:
    # -q query only, -u unprivileged port (classic; NTPsec ignores it),
    # -t per-reply timeout (both implementations accept it).
    cmd = [ntpdate, "-q", "-u", "-t", "%g" % query_timeout, source]
    env = dict(os.environ)
    env.update(LC_ALL="C", LANG="C", PATH=SAFE_PATH + os.pathsep + os.environ.get("PATH", ""))
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              stdin=subprocess.DEVNULL, env=env, timeout=max_wait,
                              universal_newlines=True, errors="replace")
    except subprocess.TimeoutExpired:
        return Result(source=source, state="TIMEOUT",
                      detail="ntpdate did not finish within %g s" % max_wait)
    except OSError as exc:
        return Result(source=source, state="ERROR", detail="could not run ntpdate: %s" % exc)
    return parse_output(source, proc.stdout or "")


def run_queries(ntpdate: str, sources: Sequence[str], query_timeout: float,
                max_wait: float, workers: int) -> List[Result]:
    workers = max(1, min(workers, len(sources)))
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        return list(pool.map(lambda s: query_source(ntpdate, s, query_timeout, max_wait),
                             sources))


# ---------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------

@dataclass
class Summary:
    status: str = "OK"
    polled: int = 0
    usable: int = 0
    combined: Optional[float] = None
    median: Optional[float] = None
    minimum: Optional[Result] = None
    maximum: Optional[Result] = None
    spread: Optional[float] = None
    stdev: Optional[float] = None
    findings: List[Tuple[str, str]] = field(default_factory=list)
    failed: List[Result] = field(default_factory=list)

    def raise_to(self, level: str, text: str) -> None:
        self.findings.append((level, text))
        if STATUS_RANK[level] > STATUS_RANK[self.status]:
            self.status = level


def level_for(abs_offset: float, warn_s: float, crit_s: float) -> str:
    if abs_offset >= crit_s:
        return "CRIT"
    if abs_offset >= warn_s:
        return "WARN"
    return "OK"


def evaluate(results: List[Result], warn_ms: float, crit_ms: float) -> Summary:
    warn_s, crit_s = warn_ms / 1000.0, crit_ms / 1000.0
    s = Summary(polled=len(results))
    good = [r for r in results if r.usable]
    s.usable = len(good)
    s.failed = [r for r in results if not r.usable]
    for r in s.failed:
        r.status = r.state

    if not good:
        s.raise_to("CRIT", "No source returned a usable reply, so no combined offset "
                           "could be computed.")
    else:
        offsets = [r.offset for r in good]
        s.combined = statistics.mean(offsets)
        s.median = statistics.median(offsets)
        s.minimum = min(good, key=lambda r: r.offset)
        s.maximum = max(good, key=lambda r: r.offset)
        s.spread = s.maximum.offset - s.minimum.offset
        s.stdev = statistics.stdev(offsets) if len(offsets) >= 2 else None

        outliers = []
        for r in good:
            r.dev = r.offset - s.combined
            if len(good) >= 3 and abs(r.offset - s.median) >= warn_s:
                r.status = "OUTLIER"
                outliers.append(r)
            else:
                r.status = level_for(abs(r.offset), warn_s, crit_s)

        level = level_for(abs(s.combined), warn_s, crit_s)
        if level != "OK":
            limit = crit_ms if level == "CRIT" else warn_ms
            s.raise_to(level, "Combined offset %s ms is at or above the %s threshold (%g ms)."
                       % (fmt_ms(s.combined, signed=True), level, limit))
        if outliers:
            names = ", ".join("%s (%s ms)" % (r.source, fmt_ms(r.offset, signed=True))
                              for r in outliers)
            s.raise_to("WARN", "%d source%s disagree%s with the median by %g ms or more: %s"
                       % (len(outliers), "" if len(outliers) == 1 else "s",
                          "s" if len(outliers) == 1 else "", warn_ms, names))
        elif len(good) >= 2 and s.spread >= warn_s:
            s.raise_to("WARN", "Sources disagree by %s ms (max - min), at or above the WARN "
                               "threshold." % fmt_ms(s.spread))

    if s.failed:
        s.raise_to("WARN", "%d of %d sources did not return a usable reply:"
                   % (len(s.failed), len(results)))
    return s


# ---------------------------------------------------------------------------
# Report rendering
# ---------------------------------------------------------------------------

Line = Tuple[str, Optional[str]]   # (text, highlight level for HTML or None)


def fmt_ms(seconds: Optional[float], signed: bool = False) -> str:
    if seconds is None:
        return "-"
    return ("%+.3f" if signed else "%.3f") % (seconds * 1000.0)


def shorten(text: str, width: int = MAX_NAME_WIDTH) -> str:
    return text if len(text) <= width else text[:width - 3] + "..."


def render_table(headers: Sequence[str], aligns: str, rows: List[Tuple[List[str], Optional[str]]],
                 footer: List[Tuple[str, Dict[int, str], Optional[str]]]) -> List[Line]:
    """Aligned text table. Footer label spans the columns before its first value."""
    widths = [len(h) for h in headers]
    for cells, _ in rows:
        for i, cell in enumerate(cells):
            widths[i] = max(widths[i], len(cell))
    for _, cols, _ in footer:
        for i, cell in cols.items():
            widths[i] = max(widths[i], len(cell))
    for label, cols, _ in footer:
        first = min(cols) if cols else len(widths)
        span = sum(widths[:first]) + 2 * (first - 1)
        if len(label) > span:
            widths[0] += len(label) - span

    def fmt(cells: Sequence[str]) -> str:
        out = []
        for i, cell in enumerate(cells):
            out.append(cell.ljust(widths[i]) if aligns[i] == "L" else cell.rjust(widths[i]))
        return "  ".join(out).rstrip()

    rule = "  ".join("-" * w for w in widths)
    lines: List[Line] = [(fmt(headers), None), (rule, None)]
    lines += [(fmt(cells), level) for cells, level in rows]
    if footer:
        lines.append((rule, None))
        for label, cols, level in footer:
            first = min(cols) if cols else len(widths)
            span = sum(widths[:first]) + 2 * (first - 1)
            rest = [cols.get(i, "") for i in range(first, len(widths))]
            tail = "  ".join(c.ljust(widths[first + j]) if aligns[first + j] == "L"
                             else c.rjust(widths[first + j]) for j, c in enumerate(rest))
            lines.append(((label.ljust(span) + "  " + tail).rstrip(), level))
    return lines


def row_level(status: str) -> Optional[str]:
    if status == "OK":
        return None
    if status == "CRIT":
        return "CRIT"
    return "WARN"


def build_report(results: List[Result], s: Summary, meta: Dict[str, str],
                 flavor: str, warn_ms: float, crit_ms: float) -> List[Line]:
    delay_hdr = "+/- ms" if flavor == "ntpsec" else "Delay ms"
    headers = ["Source", "Address", "Stratum", "Offset ms", delay_hdr, "Dev ms", "Status"]
    rows = []
    for r in results:
        cells = [shorten(r.source), shorten(r.address),
                 str(r.stratum) if r.stratum is not None else "-",
                 fmt_ms(r.offset, signed=True) if r.usable else "-",
                 fmt_ms(r.delay) if r.usable else "-",
                 fmt_ms(r.dev, signed=True) if r.usable else "-",
                 r.status]
        rows.append((cells, row_level(r.status)))
    footer = [("COMBINED (mean of %d)" % s.usable,
               {3: fmt_ms(s.combined, signed=True) if s.combined is not None else "n/a"},
               row_level(s.status))]
    table = render_table(headers, "LLRRRRL", rows, footer)

    width = max(72, max(len(t) for t, _ in table))
    heavy, light = "=" * width, "-" * width
    out: List[Line] = []

    def add(text: str = "", level: Optional[str] = None) -> None:
        out.append((text, level))

    def kv(label: str, value: str, level: Optional[str] = None) -> None:
        add("%-17s: %s" % (label, value), level)

    add("NTP TIME SOURCE REPORT")
    add(heavy)
    kv("Host", meta["host"])
    kv("Generated", meta["generated"])
    kv("ntpdate", meta["ntpdate"])
    kv("Overall status", s.status, s.status)
    if s.combined is not None:
        kv("Combined offset", "%s ms  (mean of %d usable replies, %d sources polled)"
           % (fmt_ms(s.combined, signed=True), s.usable, s.polled), row_level(s.status))
    else:
        kv("Combined offset", "n/a  (0 usable replies, %d sources polled)" % s.polled, "CRIT")
    add()

    add("SOURCES")
    add(light)
    out.extend(table)
    add()

    add("STATISTICS (usable replies only)")
    add(light)
    if s.combined is None:
        add("No usable replies.")
    else:
        stats = [
            ("Combined (mean)", fmt_ms(s.combined, signed=True), ""),
            ("Median", fmt_ms(s.median, signed=True), ""),
            ("Minimum", fmt_ms(s.minimum.offset, signed=True), s.minimum.source),
            ("Maximum", fmt_ms(s.maximum.offset, signed=True), s.maximum.source),
            ("Spread (max-min)", fmt_ms(s.spread), ""),
            ("Std deviation", fmt_ms(s.stdev) if s.stdev is not None else "n/a", ""),
        ]
        vw = max(len(v) for _, v, _ in stats)
        for label, value, note in stats:
            unit = " ms" if value != "n/a" else "   "
            kv(label, (value.rjust(vw) + unit + ("   (%s)" % note if note else "")).rstrip())
    kv("Thresholds", "WARN >= %g ms, CRIT >= %g ms" % (warn_ms, crit_ms))
    add()

    add("FINDINGS")
    add(light)
    if not s.findings:
        add("* All sources replied and agree within thresholds.", "OK")
    for level, text in s.findings:
        add("* [%s] %s" % (level, text), level)
        if text.endswith("usable reply:"):     # list the failed sources under it
            nw = max(len(shorten(r.source)) for r in s.failed)
            sw = max(len(r.state) for r in s.failed)
            for r in s.failed:
                add("    - %s  %s  %s" % (shorten(r.source).ljust(nw), r.state.ljust(sw),
                                          r.detail), "WARN")
    add()

    add("LEGEND")
    add(light)
    add("Offset ms  correction this host needs to match the source;")
    add("           positive means this host's clock is BEHIND the source.")
    if flavor == "ntpsec":
        add("+/- ms     ntpdig error bound: half the round-trip delay plus clock")
        add("           precision (the NTPsec ntpdate does not print raw delay).")
    else:
        add("Delay ms   round-trip network delay to the source.")
    add("Dev ms     source offset minus the combined offset.")
    add("COMBINED   arithmetic mean of the offsets of all usable replies.")
    add("OUTLIER    differs from the median of all sources by >= the WARN threshold.")
    add()
    add("Generated by %s on %s in %s s." % (meta["script"], meta["host"], meta["elapsed"]))
    return out


HTML_COLORS = {"OK": "#1a7f37", "WARN": "#9a6700", "CRIT": "#cf222e"}


def to_html(lines: List[Line], title: str) -> str:
    body = []
    for text, level in lines:
        esc = html.escape(text)
        if level in HTML_COLORS and text.strip():
            esc = '<span style="color:%s;">%s</span>' % (HTML_COLORS[level], esc)
        body.append(esc)
    return (
        "<!DOCTYPE html>\n"
        "<html><head><meta http-equiv=\"Content-Type\" content=\"text/html; charset=us-ascii\">"
        "<title>%s</title></head>\n"
        "<body style=\"margin:0;padding:16px;background:#ffffff;\">\n"
        "<pre style=\"font-family:Consolas,'Courier New',Menlo,monospace;font-size:13px;"
        "line-height:1.4;color:#1f2328;margin:0;\">%s</pre>\n"
        "</body></html>\n" % (html.escape(title), "\n".join(body))
    )


def build_subject(prefix: str, s: Summary, host: str) -> str:
    if s.combined is None:
        return "[%s %s] %s: no NTP source returned a usable reply (0/%d)" % (
            prefix, s.status, host, s.polled)
    return "[%s %s] %s: combined offset %s ms, %d/%d sources usable" % (
        prefix, s.status, host, fmt_ms(s.combined, signed=True), s.usable, s.polled)


# ---------------------------------------------------------------------------
# Email
# ---------------------------------------------------------------------------

def ascii_only(text: str) -> str:
    return text.encode("ascii", "replace").decode("ascii")


def split_addresses(values: Sequence[str]) -> List[str]:
    out = []
    for value in values:
        out.extend(a.strip() for a in value.split(",") if a.strip())
    return out


def parse_smtp(target: str, use_ssl: bool, starttls: bool) -> Tuple[str, int]:
    default_port = 465 if use_ssl else (587 if starttls else 25)
    host, port = target, default_port
    if target.startswith("["):                     # [IPv6]:port
        host, _, rest = target[1:].partition("]")
        if rest.startswith(":"):
            port = int(rest[1:])
    elif target.count(":") == 1:
        host, port_text = target.split(":")
        port = int(port_text)
    return host, port


def send_email(args: argparse.Namespace, recipients: List[str], subject: str,
               text: str, html_body: str) -> None:
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = args.mail_from or "ntp-report@%s" % socket.getfqdn()
    msg["To"] = ", ".join(recipients)
    msg["Date"] = formatdate(localtime=True)
    msg["Message-ID"] = make_msgid()
    # Plain 7-bit ASCII keeps the raw message readable (no base64) and is
    # valid as long as lines stay under the 998 character SMTP limit.
    msg.set_content(ascii_only(text), charset="us-ascii", cte="7bit")
    msg.add_alternative(ascii_only(html_body), subtype="html", charset="us-ascii", cte="7bit")

    if args.sendmail:
        subprocess.run([args.sendmail_path, "-t", "-oi"], input=msg.as_bytes(),
                       check=True, timeout=60)
        return

    host, port = parse_smtp(args.smtp, args.ssl, args.starttls)
    context = ssl.create_default_context()
    if args.ssl:
        server = smtplib.SMTP_SSL(host, port, timeout=30, context=context)
    else:
        server = smtplib.SMTP(host, port, timeout=30)
    with server:
        if args.starttls:
            server.starttls(context=context)
        if args.smtp_user:
            password = os.environ.get("NTP_REPORT_SMTP_PASSWORD")
            if password is None:
                raise RuntimeError("--smtp-user given but NTP_REPORT_SMTP_PASSWORD is not set")
            server.login(args.smtp_user, password)
        server.send_message(msg)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def load_sources(args: argparse.Namespace) -> List[str]:
    items = list(args.sources)
    for path in args.file:
        with open(path, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                words = line.split("#", 1)[0].split()
                if words:
                    items.append(words[0])
    if not items:
        items = list(DEFAULT_SOURCES)
    seen, out = set(), []
    for item in items:
        if item.startswith("-") or not SOURCE_RE.match(item):
            raise ValueError("invalid source name: %r" % item)
        if item.lower() not in seen:
            seen.add(item.lower())
            out.append(item)
    return out


def parse_args(argv: Optional[Sequence[str]]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Query NTP sources with 'ntpdate -q' and build an email report.",
        epilog="Exit status: 0 OK, 1 WARN, 2 CRIT, 3 UNKNOWN.")
    p.add_argument("sources", nargs="*", metavar="SOURCE",
                   help="NTP server hostname or IP (default: built-in list)")
    p.add_argument("-f", "--file", action="append", default=[], metavar="PATH",
                   help="file with one source per line (may be repeated)")
    p.add_argument("--warn-ms", type=float, default=DEFAULT_WARN_MS,
                   help="WARN threshold in ms (default %(default)g)")
    p.add_argument("--crit-ms", type=float, default=DEFAULT_CRIT_MS,
                   help="CRIT threshold in ms (default %(default)g)")
    p.add_argument("--ntpdate", metavar="PATH", help="path to ntpdate (default: search PATH)")
    p.add_argument("--query-timeout", type=float, default=2.0, metavar="SEC",
                   help="seconds ntpdate waits for each reply, passed as -t (default %(default)g)")
    p.add_argument("--max-wait", type=float, default=30.0, metavar="SEC",
                   help="hard time limit for each ntpdate run (default %(default)g)")
    p.add_argument("--workers", type=int, default=8,
                   help="sources queried in parallel (default %(default)d)")
    p.add_argument("--print", dest="print_report", action="store_true",
                   help="also print the text report to stdout when emailing")

    g = p.add_argument_group("email (report is printed to stdout if --to is not given)")
    g.add_argument("--to", action="append", default=[], metavar="ADDR",
                   help="recipient; may be repeated or comma separated")
    g.add_argument("--from", dest="mail_from", metavar="ADDR",
                   help="sender (default ntp-report@<fqdn>)")
    g.add_argument("--subject-prefix", default="NTP", metavar="TEXT",
                   help="tag in the subject, e.g. [NTP OK] (default %(default)s)")
    g.add_argument("--mail-on", choices=("always", "warn", "crit"), default="always",
                   help="send only when status is at least this level (default %(default)s)")
    g.add_argument("--smtp", default="localhost", metavar="HOST[:PORT]",
                   help="SMTP relay (default %(default)s)")
    g.add_argument("--starttls", action="store_true", help="use STARTTLS (default port 587)")
    g.add_argument("--ssl", action="store_true", help="use implicit TLS (default port 465)")
    g.add_argument("--smtp-user", metavar="USER",
                   help="SMTP login; password from NTP_REPORT_SMTP_PASSWORD")
    g.add_argument("--sendmail", action="store_true",
                   help="deliver with the local sendmail binary instead of SMTP")
    g.add_argument("--sendmail-path", default="/usr/sbin/sendmail", metavar="PATH",
                   help="sendmail binary for --sendmail (default %(default)s)")

    args = p.parse_args(argv)
    if args.warn_ms <= 0 or args.crit_ms <= args.warn_ms:
        p.error("thresholds must satisfy 0 < --warn-ms < --crit-ms")
    if args.query_timeout <= 0 or args.max_wait <= 0 or args.workers < 1:
        p.error("--query-timeout, --max-wait and --workers must be positive")
    if args.ssl and args.starttls:
        p.error("use either --ssl or --starttls, not both")
    return args


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    try:
        sources = load_sources(args)
    except (OSError, ValueError) as exc:
        print("ERROR: %s" % exc, file=sys.stderr)
        return 3

    ntpdate = find_ntpdate(args.ntpdate)
    if not ntpdate:
        print("ERROR: ntpdate not found. Install it with: sudo apt install ntpdate",
              file=sys.stderr)
        return 3

    started = time.monotonic()
    results = run_queries(ntpdate, sources, args.query_timeout, args.max_wait, args.workers)
    elapsed = time.monotonic() - started

    seen_flavors = {r.flavor for r in results if r.flavor}
    flavor = seen_flavors.pop() if len(seen_flavors) == 1 else detect_flavor(ntpdate)
    flavor_name = {"ntpsec": "NTPsec wrapper for ntpdig",
                   "classic": "NTP Classic"}.get(flavor, "unknown type")

    summary = evaluate(results, args.warn_ms, args.crit_ms)
    host = socket.getfqdn()
    meta = {
        "host": host,
        "generated": datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %Z"),
        "ntpdate": "%s (%s)" % (ntpdate, flavor_name),
        "script": os.path.basename(sys.argv[0]) or "ntp_report.py",
        "elapsed": "%.1f" % elapsed,
    }
    lines = build_report(results, summary, meta, flavor, args.warn_ms, args.crit_ms)
    text = "\n".join(t for t, _ in lines) + "\n"
    subject = build_subject(args.subject_prefix, summary, host)

    recipients = split_addresses(args.to)
    if not recipients:
        sys.stdout.write(text)
        return STATUS_RANK[summary.status]

    threshold = {"always": "OK", "warn": "WARN", "crit": "CRIT"}[args.mail_on]
    if STATUS_RANK[summary.status] >= STATUS_RANK[threshold]:
        try:
            send_email(args, recipients, subject, text, to_html(lines, subject))
        except (OSError, RuntimeError, smtplib.SMTPException,
                subprocess.SubprocessError) as exc:
            print("ERROR: could not send email: %s" % exc, file=sys.stderr)
            sys.stdout.write(text)
            return 3
    if args.print_report:
        sys.stdout.write(text)
    return STATUS_RANK[summary.status]


if __name__ == "__main__":
    sys.exit(main())
