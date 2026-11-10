#!/usr/bin/env python3
"""Re-check every quotation in `Maxwell/Sources.lean` against the scan it cites.

Each `Source` record names an Internet Archive item (`localFile` -> the `def ... : String`
above it), a locus, a page, and a quotation the library says was checked against that scan.
This script downloads the item's OCR text (cached), reduces both sides to lower-case
alphanumerics (so line breaks, end-of-line hyphenation, curly quotes, dashes and OCR word
splittings like "alge braically" do not matter), and measures how much of each quotation
occurs in its scan:

    OK       the whole quotation (short) or at least 95% of it (long) occurs in the scan
    PARTIAL  50-95% occurs: the text is there but the OCR has damaged a stretch
             (Fraktur letters, displayed formulas) - look at the page image
    MISS     under 50%: the quotation is not in that scan as transcribed

    python3 scripts/check_sources.py              # check, cache under .scratch/sources
    python3 scripts/check_sources.py --strict     # exit 1 on PARTIAL as well
    python3 scripts/check_sources.py --cache DIR

This is not a proof of fidelity. OCR of a 150-year-old book is noisy and displayed formulas
are unreadable in it; the printed formulas were checked by eye against page images instead
(see README). A PASS means the quotations are where the records say they are.
"""

import argparse
import os
import re
import sys
import urllib.request

SOURCES = "Maxwell/Sources.lean"
SHORT = 80      # quotations shorter than this many alphanumerics must match in full
WINDOW = 40     # probe length, in alphanumerics
STEP = 20       # stride between probes


def normalise(s: str) -> str:
    """Lower-case alphanumerics only: line breaks, hyphenation, punctuation, quotes and
    dashes disappear, so only OCR damage to the letters themselves can cause a mismatch."""
    for a, b in (("\u2019", "'"), ("\u2018", "'"), ("\u201c", '"'), ("\u201d", '"'),
                 ("\u2014", "-"), ("\u2013", "-"), ("\u00ad", "")):
        s = s.replace(a, b)
    s = re.sub(r"-\s*\n\s*", "", s)
    return re.sub(r"[^0-9a-z]", "", s.lower())


def parse_sources(path: str):
    """Return the `Source` records parsed from the Lean file."""
    text = open(path, encoding="utf-8").read()
    scans = dict(re.findall(r'^def (\w+) : String :=\s*"([^"]*)"', text, re.M))
    records = []
    for name, body in re.findall(r"def (\w+) : Source :=\s*\{(.*?)\n    status :=", text, re.S):
        def field(key):
            m = re.search(key + r' := "((?:[^"\\]|\\.)*)"', body, re.S)
            return None if m is None else re.sub(r"\s+", " ", m.group(1).replace("\\\n", " "))
        m = re.search(r"localFile := (\w+)", body)
        records.append({
            "name": name,
            "locus": field("locus"),
            "page": field("page"),
            "scan": scans.get(m.group(1), m.group(1)) if m else None,
            "quote": field("quote"),
        })
    return records


def fetch(scan: str, cache: str) -> str:
    """The scan's OCR text, normalised, downloaded once into `cache`."""
    os.makedirs(cache, exist_ok=True)
    path = os.path.join(cache, scan + ".txt")
    if not os.path.exists(path):
        url = f"https://archive.org/download/{scan}/{scan}_djvu.txt"
        sys.stderr.write(f"fetching {url}\n")
        with urllib.request.urlopen(url, timeout=300) as r, open(path, "wb") as f:
            f.write(r.read())
    return normalise(open(path, encoding="utf-8", errors="replace").read())


def coverage(quote: str, text: str) -> float:
    """Fraction of the quotation's character windows that occur in the scan."""
    starts = list(range(0, max(1, len(quote) - WINDOW + 1), STEP))
    if not starts:
        return 1.0 if quote in text else 0.0
    return sum(1 for s in starts if quote[s:s + WINDOW] in text) / len(starts)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--sources", default=SOURCES)
    ap.add_argument("--cache", default=os.path.join(".scratch", "sources"))
    ap.add_argument("--strict", action="store_true", help="exit 1 on PARTIAL too")
    ap.add_argument("--verbose", "-v", action="store_true")
    args = ap.parse_args()

    records = parse_sources(args.sources)
    if not records:
        print(f"no Source records found in {args.sources}", file=sys.stderr)
        return 2

    texts, counts = {}, {"OK": [], "PARTIAL": [], "MISS": []}
    for rec in records:
        scan = rec["scan"]
        if scan not in texts:
            try:
                texts[scan] = fetch(scan, args.cache)
            except Exception as exc:                    # network, 404, permissions
                print(f"ERROR {rec['name']}: cannot read scan {scan}: {exc}", file=sys.stderr)
                texts[scan] = ""
        quote = normalise(rec["quote"] or "")
        cov = coverage(quote, texts[scan])
        if len(quote) < SHORT:
            verdict = "OK" if cov == 1.0 else "MISS"
        else:
            verdict = "OK" if cov >= 0.95 else "PARTIAL" if cov >= 0.5 else "MISS"
        counts[verdict].append(rec["name"])
        print(f"{verdict:<7} {rec['name']:<30} [{scan} {rec['page']}] "
              f"{len(quote):>4} chars, {cov:.2f} found")

    print(f"\n{len(records)} records: {len(counts['OK'])} OK, "
          f"{len(counts['PARTIAL'])} PARTIAL, {len(counts['MISS'])} MISS")
    if counts["PARTIAL"]:
        print("PARTIAL (OCR damage; check the page image): " + ", ".join(counts["PARTIAL"]))
    if counts["MISS"]:
        print("MISS (not found as transcribed): " + ", ".join(counts["MISS"]))
        return 1
    if args.strict and counts["PARTIAL"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
