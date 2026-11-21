#!/usr/bin/env python3
"""Slow, literal reference from rules.md. usage: ref.py DATA OUT"""
import sys, os, re, glob, json, csv, datetime
from collections import defaultdict
D, O = sys.argv[1], sys.argv[2]

def lines(path):
    b = open(path, 'rb').read().decode('latin-1')
    parts = b.split('\n')
    if parts and parts[-1] == '':
        parts.pop()
    return parts[1:]  # drop header

def fields(line, n):
    f = line.split(',')
    if len(f) != n: return None
    out = []
    for x in f:
        if '"' in x:
            if len(x) < 2 or x[0] != '"' or x[-1] != '"' or '"' in x[1:-1]: return None
            x = x[1:-1]
        out.append(x)
    return out

R1 = re.compile(r'^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})Z$')
R2 = re.compile(r'^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})([+-])([0-9]{2}):([0-9]{2})$')
R3 = re.compile(r'^[0-9]+$')
EP = datetime.date(1970, 1, 1)
def ts(s):
    m = R1.match(s) or R2.match(s)
    if m:
        g = m.groups()
        y, mo, d, h, mi, se = map(int, g[:6])
        if h > 23 or mi > 59 or se > 59: return None
        try: dt = datetime.date(y, mo, d)
        except ValueError: return None
        t = ((dt - EP).days * 86400 + h * 3600 + mi * 60 + se) * 1000
        if len(g) == 9:
            oh, om = int(g[7]), int(g[8])
            if oh > 23 or om > 59: return None
            off = (oh * 60 + om) * 60000
            t = t - off if g[6] == '+' else t + off
        return t
    if R3.match(s):
        v = int(s)
        return v if v < 2**63 else None
    return None

man = json.load(open(f'{D}/manifest.json'))
ws, we = ts(man['window_start']), ts(man['window_end'])
DAY = 86400000; WEEK = 7 * DAY
cat = {}
for l in lines(f'{D}/products.csv'):
    f = fields(l, 2)
    if f: cat[f[0]] = f[1]
chan = {}
for l in lines(f'{D}/campaigns.csv'):
    f = fields(l, 2)
    if f: chan[f[0]] = f[1]
# links
par = {}
def find(x):
    while par.setdefault(x, x) != x:
        par[x] = par[par[x]]; x = par[x]
    return x
for p in sorted(glob.glob(f'{D}/links/*.csv')):
    for l in lines(p):
        f = fields(l, 2)
        if not f or not f[0] or not f[1]: continue
        a, b = find(f[0]), find(f[1])
        if a != b: par[a] = b
comp = defaultdict(list)
for x in list(par): comp[find(x)].append(x)
name = {}
for r, ms in comp.items():
    nm = min(ms)
    for x in ms: name[x] = nm
def person(u): return name.get(u, u)
# events
best = {}
for p in sorted(glob.glob(f'{D}/events/*.csv')):
    for l in lines(p):
        f = fields(l, 7)
        if not f or not f[0]: continue
        i = ts(f[3])
        i = i if i is not None else 1 << 62
        o = best.get(f[0])
        if o is None or i < o[0]: best[f[0]] = (i, f)
evs = defaultdict(list)
for i, f in best.values():
    _, u, t, _, ty, pr, price = f
    t = ts(t)
    if not u or t is None or not (ws <= t < we) or ty not in ('view', 'cart', 'purchase') or not pr: continue
    pv = 0
    if ty == 'purchase':
        if not re.fullmatch(r'[0-9]+', price) or not (1 <= int(price) <= 10_000_000): continue
        pv = int(price)
    if i - t > DAY: continue
    evs[person(u)].append((t, ty == 'purchase', pv, cat.get(pr, 'unknown')))
clicks = defaultdict(dict)
for p in sorted(glob.glob(f'{D}/clicks/*.csv')):
    for l in lines(p):
        f = fields(l, 4)
        if not f or not f[0] or not f[1]: continue
        t = ts(f[3])
        if t is None or not (ws - WEEK <= t < we) or f[2] not in chan: continue
        clicks[person(f[1])][f[0]] = (t, f[0], f[2])
U = defaultdict(lambda: [0, 0, 0, defaultdict(int)])
C = defaultdict(lambda: [0, 0, 0, 0])
for pn, es in evs.items():
    es.sort(key=lambda e: e[0])
    cs = list(clicks.get(pn, {}).values())
    sess = []
    for e in es:
        if not sess or e[0] - sess[-1][-1][0] > 1800000: sess.append([e])
        else: sess[-1].append(e)
    for s in sess:
        st = s[0][0]
        day = EP + datetime.timedelta(days=st // DAY)
        qual = [c for c in cs if c[0] <= st and st - c[0] <= WEEK]
        if qual:
            mx = max(c[0] for c in qual)
            cid = min(c for c in qual if c[0] == mx)[2]
        else: cid = 'organic'
        rev = sum(e[2] for e in s); pur = any(e[1] for e in s)
        u = U[(pn, day)]; u[0] += 1; u[1] += len(s); u[2] += rev
        for e in s:
            if e[1]: u[3][e[3]] += e[2]
        c = C[(cid, day)]; c[0] += 1; c[1] += pur; c[2] += rev
        for a in {c2[2] for c2 in qual}: C[(a, day)][3] += 1
os.makedirs(O, exist_ok=True)
with open(f'{O}/user_daily.csv', 'w') as fo:
    fo.write('user_id,day,sessions,events,revenue_cents,top_category\n')
    for (pn, d), (s, e, r, cs) in U.items():
        top = ''
        if cs:
            top = sorted(cs.items(), key=lambda kv: (-kv[1], kv[0].encode('latin-1')))[0][0]
        fo.write(f'{pn},{d},{s},{e},{r},{top}\n')
with open(f'{O}/campaign_daily.csv', 'w') as fo:
    fo.write('campaign_id,channel,day,sessions,purchasing_sessions,revenue_cents,assisted_sessions\n')
    for (cid, d), (s, p, r, a) in C.items():
        fo.write(f'{cid},{"organic" if cid=="organic" else chan[cid]},{d},{s},{p},{r},{a}\n')
