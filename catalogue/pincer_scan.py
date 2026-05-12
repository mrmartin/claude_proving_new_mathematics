#!/usr/bin/env python3
"""Pincer scan v4 — soft blocker penalty + better pincer pattern recognition."""
import re, html, glob, json

# Patterns
LOWER_PATTERNS = [
    (r'\$\d+\s*\\leq\s+[a-zA-Z]\s*\\leq\s*\d+\$', 'range a≤k≤b'),
    (r'\$\d+\s*\\le\s+[a-zA-Z]\s*\\le\s*\d+\$', 'range a≤k≤b'),
    (r'\$[a-zA-Z]\s*\\leq\s*\d+\$', 'k ≤ N (explicit)'),
    (r'verified (?:this is true,? )?for [^.]{0,80}', 'verified for ...'),
    (r'has(?:\s+been)?\s+verified for [^.]{0,80}', 'verified for ...'),
    (r'no (?:such|other) (?:n|k|triple|example|solution|counterexample)s?\s*(?:for|with|below)?\s*[^.]{0,80}', 'no such ...'),
    (r'(?:proved|shown|established) (?:this )?is impossible (?:when|for)\s+\$?[\d\w][^.]{0,60}', 'impossible for ...'),
    (r'There are no(?: other)? solutions (?:below|less than|with)', 'no solutions below'),
    (r'(?:checked|computed|enumerated|searched)\s+(?:up\s+to|to|for(?:\s+all)?)', 'checked up to'),
]
UPPER_PATTERNS = [
    (r'(?:for|when)\s+\$?[a-zA-Z]\$?\s+(?:is\s+)?sufficiently\s+large', 'k sufficiently large'),
    (r'for sufficiently large\s+\$?[a-zA-Z]\$?', 'sufficiently large k'),
    (r'(?:proved|shown) (?:this|that) (?:is )?(?:impossible|true|holds|finite) (?:for|when)?\s*(?:all )?\$?[a-zA-Z]\$?\s+sufficiently\s+large', 'shown for sufficiently large'),
    (r'only finitely many', 'only finitely many'),
    (r'all but (?:at most )?finitely many', 'all but finitely many'),
    (r'is only possible for\s+\$?[a-zA-Z]?\s*\\ll', 'only possible for ≪'),
    (r'depending only on', 'effective depending only on'),
    (r'is finite (?:for all|when)\s+[a-zA-Z]\s*\\geq', 'finite for k ≥'),
    (r'\$[a-zA-Z]\s*\\geq\s*[^$]{1,40}\$', 'k ≥ ...'),
]
# These conjecture mentions DO block: if the problem's only known asymptotic depends on these
HARD_BLOCKERS = [
    'Riemann Hypothesis', 'GRH', 'RH',
]
# Soft blockers — flag but don't disqualify; the problem may still have a separate unconditional path
SOFT_BLOCKERS = [
    'abc conjecture', 'ABC conjecture',
    'Legendre',
    'Schinzel', 'Hypothesis H',
    'Vojta', 'Bombieri-Lang', 'Lang conjecture',
    'twin prime',
    'Hardy-Littlewood',
    'Elliott-Halberstam',
    'Mertens conjecture',
    'Birch and Swinnerton-Dyer',
    "Cramér's conjecture", "Cramer's conjecture",
    'Polignac',
    'Continuum Hypothesis',
    'transcendence',
    'Goldbach',
]
# Phrases that indicate the problem is essentially HOPELESS or Erdős believed unreachable
HOPELESS = [
    'almost certainly true, but the proof is beyond',
    'beyond our ability',
    'hopeless',
    'extremely doubtful',
    'intractable at present',
    'notoriously difficult',
]

def extract_remarks(html_str):
    t = re.sub(r'<script[\s\S]*?</script>', '', html_str)
    t = re.sub(r'<style[\s\S]*?</style>', '', t)
    txt = re.sub(r'<[^>]+>', ' ', t)
    txt = html.unescape(txt)
    txt = re.sub(r'\s+', ' ', txt).strip()
    i = txt.rfind('Random Open')
    if i > 0: txt = txt[i+len('Random Open'):]
    for e in ['View the LaTeX source', 'External data from the database', 'Comment activity']:
        j = txt.find(e)
        if j > 0: txt = txt[:j]; break
    return txt.strip()

def status_of(t):
    for s in ('VERIFIABLE','FALSIFIABLE','OPEN'):
        if s in t: return s
    return None

def match_patterns(text, patterns):
    hits = []
    for pat, desc in patterns:
        try:
            for m in re.finditer(pat, text):
                hits.append((desc, m.group(0)[:120]))
        except re.error:
            pass
    return hits

def find_any(text, lst):
    return [b for b in lst if b.lower() in text.lower()]

results = []
for path in sorted(glob.glob('/tmp/erdos_pages/p*.html')):
    n = int(re.search(r'p(\d+)\.html', path).group(1))
    rem = extract_remarks(open(path).read())
    if len(rem) < 200: continue
    st = status_of(rem)
    if not st: continue
    lower_hits = match_patterns(rem, LOWER_PATTERNS)
    upper_hits = match_patterns(rem, UPPER_PATTERNS)
    hard_b = find_any(rem, HARD_BLOCKERS)
    soft_b = find_any(rem, SOFT_BLOCKERS)
    hopeless = find_any(rem, HOPELESS)
    distinct_lower = len(set(d for d,_ in lower_hits))
    distinct_upper = len(set(d for d,_ in upper_hits))
    score = 0
    if lower_hits: score += 3
    if upper_hits: score += 3
    if lower_hits and upper_hits: score += 8
    score += distinct_lower + distinct_upper
    score -= 6 * len(hard_b)
    score -= 1 * len(soft_b)
    score -= 5 * len(hopeless)
    results.append({
        'n': n, 'status': st, 'score': score,
        'L': distinct_lower, 'U': distinct_upper,
        'lower_hits': lower_hits, 'upper_hits': upper_hits,
        'hard_blockers': hard_b, 'soft_blockers': soft_b,
        'hopeless': hopeless,
        'remarks_len': len(rem),
        'remarks': rem,
    })

# Strong = both bounds present, no hard blockers, not declared hopeless
strong = [r for r in results
          if r['lower_hits'] and r['upper_hits']
          and not r['hard_blockers']
          and not r['hopeless']]
strong.sort(key=lambda x: -x['score'])

print(f'Scanned: {len(results)} open problems')
print(f'Strong candidates: {len(strong)}\n')

for i, r in enumerate(strong[:25]):
    rm = r['remarks']
    for cut in ['claimed in the comments.', 'finite counterexample.', 'a finite example.']:
        j = rm.find(cut)
        if j > 0:
            rm = rm[j+len(cut):]; break
    rm = rm.strip()
    soft_note = f" soft-blockers={r['soft_blockers']}" if r['soft_blockers'] else ""
    print(f"\n#{i+1}. Problem #{r['n']} ({r['status']}) score={r['score']} L={r['L']} U={r['U']}{soft_note}")
    print(f"   Lower-side claims:")
    for d, m in r['lower_hits'][:5]:
        print(f"     • [{d}] {m.strip()}")
    print(f"   Upper-side claims:")
    for d, m in r['upper_hits'][:5]:
        print(f"     • [{d}] {m.strip()}")
    if len(rm) > 900: rm = rm[:900] + '…'
    print(f"   Remarks excerpt: {rm}")

with open('/tmp/pincer_ranking4.json', 'w') as f:
    json.dump([{k: v for k, v in r.items() if k != 'remarks'} for r in results], f, indent=1)
print(f'\nFull ranking → /tmp/pincer_ranking4.json')
