#!/usr/bin/env python3
"""
Scrape erdosproblems.com/<N> for N in 1..MAX_ID and write one JSON record per
line to catalogue/erdosproblems.jsonl.

Each record captures, when present, the page's status ("open", "solved",
"disproved", "disproved (lean)", ...), the problem statement HTML+text, the
"additional text" (where partial results, counterexamples and references
appear), the tag list, and whether the page links to a formal-conjectures
file.

Resumable: if the output file already contains records, those IDs are skipped
unless --force is passed.

Polite by default: 0.5s sleep between requests, single Firefox-like
User-Agent, single requests.Session for connection reuse.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime
import json
import os
import re
import sys
import time
from pathlib import Path
from typing import Optional

import requests
from bs4 import BeautifulSoup, Tag

USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64; rv:120.0) Gecko/20100101 Firefox/120.0"
)
BASE_URL = "https://www.erdosproblems.com"
DEFAULT_MAX_ID = 1217
DEFAULT_OUT = Path(__file__).resolve().parent.parent / "catalogue" / "erdosproblems.jsonl"


@dataclasses.dataclass
class Record:
    id: int
    url: str
    exists: bool
    fetched_at: str
    http_status: int
    title: Optional[str] = None
    status_id: Optional[str] = None
    status_label: Optional[str] = None
    status_tooltip: Optional[str] = None
    statement_html: Optional[str] = None
    statement_text: Optional[str] = None
    references: Optional[str] = None
    tags: Optional[list] = None
    additional_text_html: Optional[str] = None
    additional_text_text: Optional[str] = None
    formalised_in_formal_conjectures: Optional[bool] = None
    formalised_url: Optional[str] = None
    prize: Optional[str] = None


def fetch(session: requests.Session, n: int, retries: int = 3, backoff: float = 1.5) -> tuple[int, str]:
    url = f"{BASE_URL}/{n}"
    for attempt in range(1, retries + 1):
        try:
            r = session.get(url, timeout=30)
            if r.status_code >= 500 and attempt < retries:
                time.sleep(backoff ** attempt)
                continue
            return r.status_code, r.text
        except requests.RequestException as exc:
            if attempt == retries:
                raise
            time.sleep(backoff ** attempt)
    raise RuntimeError("unreachable")


def _text(node: Optional[Tag]) -> Optional[str]:
    if node is None:
        return None
    return re.sub(r"\s+", " ", node.get_text(" ", strip=True)).strip() or None


def _inner_html(node: Optional[Tag]) -> Optional[str]:
    if node is None:
        return None
    return node.decode_contents().strip() or None


def parse(n: int, http_status: int, html: str) -> Record:
    fetched_at = datetime.datetime.now(datetime.timezone.utc).isoformat()
    url = f"{BASE_URL}/{n}"
    soup = BeautifulSoup(html, "lxml")

    title_tag = soup.find("title")
    title = title_tag.get_text(strip=True) if title_tag else None
    expected_title_prefix = f"{n} |"
    is_problem_page = bool(title and title.startswith(expected_title_prefix))

    rec = Record(
        id=n,
        url=url,
        exists=is_problem_page,
        fetched_at=fetched_at,
        http_status=http_status,
        title=title,
    )

    if not is_problem_page:
        return rec

    # Main problem-text div: pick the *first* div.problem-text whose id is
    # not "disclaimer" or "citation" — that's the live problem.
    problem_div = None
    for d in soup.find_all("div", class_="problem-text"):
        did = d.get("id", "")
        if did and did not in {"disclaimer", "citation"}:
            problem_div = d
            break
    if problem_div is None:
        problem_div = soup.find("div", class_="problem-text")

    if problem_div is not None:
        rec.status_id = problem_div.get("id")

        prize_div = problem_div.find("div", id="prize")
        if prize_div is not None:
            tooltip = prize_div.find("span", class_="tooltip")
            if tooltip is not None:
                # Direct text (excluding child tooltiptext)
                tooltiptext = tooltip.find("span", class_="tooltiptext")
                tip_text = _text(tooltiptext) if tooltiptext else None
                if tooltiptext is not None:
                    tooltiptext.extract()
                label = _text(tooltip)
                rec.status_label = label
                rec.status_tooltip = tip_text
            # Capture any prize/bounty text within prize_div not covered above
            prize_text = _text(prize_div)
            if prize_text and prize_text != rec.status_label:
                rec.prize = prize_text

        content_div = problem_div.find("div", id="content")
        rec.statement_html = _inner_html(content_div)
        rec.statement_text = _text(content_div)

        problem_id_div = problem_div.find("div", id="problem_id")
        rec.references = _text(problem_id_div)

        tags_div = problem_div.find("div", id="tags")
        if tags_div is not None:
            rec.tags = [a.get_text(strip=True) for a in tags_div.find_all("a")]

    # Additional text(s): joined together preserving order, ignoring trailing
    # "View the LaTeX source" and "View history" footer lines which we strip.
    additional_html_parts: list[str] = []
    additional_text_parts: list[str] = []
    for d in soup.find_all("div", class_="problem-additional-text"):
        for p in d.find_all("p", recursive=False):
            t = p.get_text(" ", strip=True)
            if "View the LaTeX source" in t or "View history" in t:
                p.extract()
        h = _inner_html(d)
        t = _text(d)
        if h:
            additional_html_parts.append(h)
        if t:
            additional_text_parts.append(t)
    if additional_html_parts:
        rec.additional_text_html = "\n\n".join(additional_html_parts)
    if additional_text_parts:
        rec.additional_text_text = "\n\n".join(additional_text_parts)

    # Formalised statement link.  The phrase "Formalised statement?" sits at
    # the top of an external block; the answer ("Yes" anchor / "No" text)
    # follows immediately.  We walk forward from the text node to find the
    # next anchor pointing at formal-conjectures, stopping if we hit an
    # anchor for an unrelated section (OEIS, forum, tags, etc.).
    marker = soup.find(string=lambda s: isinstance(s, str) and "Formalised statement?" in s)
    if marker is not None:
        link = None
        for a_tag in marker.find_all_next("a"):
            href = a_tag.get("href", "")
            anchor_text = a_tag.get_text(" ", strip=True)
            # The "Yes" answer points to a specific .lean file inside
            # FormalConjectures/.  The "No" answer renders as
            #   No (<a href="https://github.com/google-deepmind/formal-conjectures">
            #       Create a formalisation here</a>)
            # which we must ignore.
            if "/FormalConjectures/" in href and href.endswith(".lean"):
                link = href
                break
            if "Create a formalisation here" in anchor_text:
                # Confirmed "No" answer.
                break
            if any(s in href for s in ("oeis.org", "/forum", "/tags",
                                        "/latex/", "/history/", "/bibs/",
                                        "github.com/teorth")):
                break
        if link is not None:
            rec.formalised_in_formal_conjectures = True
            rec.formalised_url = link
        else:
            tail = (marker.split("Formalised statement?", 1)[1].strip()
                    if "Formalised statement?" in marker else "")
            tail_combined = (tail + " " + marker.parent.get_text(" ", strip=True)).strip()
            if re.search(r"Formalised statement\?\s*No\b", tail_combined):
                rec.formalised_in_formal_conjectures = False

    return rec


def already_done(out_path: Path) -> set[int]:
    if not out_path.exists():
        return set()
    done: set[int] = set()
    with out_path.open("r", encoding="utf-8") as f:
        for line in f:
            try:
                obj = json.loads(line)
                if isinstance(obj.get("id"), int):
                    done.add(obj["id"])
            except json.JSONDecodeError:
                continue
    return done


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--start", type=int, default=1)
    p.add_argument("--end", type=int, default=DEFAULT_MAX_ID)
    p.add_argument("--out", type=Path, default=DEFAULT_OUT)
    p.add_argument("--sleep", type=float, default=0.5,
                   help="seconds to wait between requests")
    p.add_argument("--force", action="store_true",
                   help="re-fetch IDs already present in --out")
    p.add_argument("--limit", type=int, default=None,
                   help="stop after this many newly-fetched problems")
    args = p.parse_args(argv)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    seen = set() if args.force else already_done(args.out)
    if seen:
        print(f"resuming: {len(seen)} IDs already present in {args.out}", file=sys.stderr)

    session = requests.Session()
    session.headers.update({"User-Agent": USER_AGENT, "Accept": "text/html"})

    fetched = 0
    with args.out.open("a", encoding="utf-8") as out_fh:
        for n in range(args.start, args.end + 1):
            if n in seen:
                continue
            try:
                http_status, html = fetch(session, n)
            except Exception as exc:
                err = {
                    "id": n,
                    "url": f"{BASE_URL}/{n}",
                    "exists": False,
                    "fetched_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    "http_status": -1,
                    "fetch_error": str(exc),
                }
                out_fh.write(json.dumps(err, ensure_ascii=False) + "\n")
                out_fh.flush()
                print(f"#{n}: ERROR {exc}", file=sys.stderr)
                time.sleep(args.sleep)
                continue
            try:
                rec = parse(n, http_status, html)
            except Exception as exc:
                err = {
                    "id": n,
                    "url": f"{BASE_URL}/{n}",
                    "exists": False,
                    "fetched_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    "http_status": http_status,
                    "parse_error": str(exc),
                }
                out_fh.write(json.dumps(err, ensure_ascii=False) + "\n")
                out_fh.flush()
                print(f"#{n}: PARSE ERROR {exc}", file=sys.stderr)
                time.sleep(args.sleep)
                continue
            row = json.dumps(dataclasses.asdict(rec), ensure_ascii=False)
            out_fh.write(row + "\n")
            out_fh.flush()
            fetched += 1
            tag = rec.status_label or ("missing" if not rec.exists else "?")
            tag_extra = ""
            if rec.formalised_in_formal_conjectures is True:
                tag_extra = " formalised"
            print(f"#{n}: {tag}{tag_extra}", file=sys.stderr)
            if args.limit is not None and fetched >= args.limit:
                break
            time.sleep(args.sleep)
    print(f"done; fetched {fetched} new records into {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
