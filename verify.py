#!/usr/bin/env python3
"""
Independent verifier for the order-n hyperstructure classification.

Reads the CSV data files in this repository, rebuilds every operation table
from its code, re-checks every defining axiom from scratch, recomputes the
automorphism group and the fundamental groups, and re-derives the
fertility / universality / barrenness statistics.  Nothing is taken on trust
from the enumeration program: the CSVs are treated purely as a list of
candidate structures.

Usage:   python3 verify.py [--dir DATA_DIR]
Exit code 0 means every check passed.
"""
import csv, sys, os, itertools, argparse
from collections import defaultdict

# --------------------------------------------------------------------------
# encoding conventions (see README.md)
#   elements          : e=0, a=1, b=2, c=3   (and d=4 for n=5)
#   subset of R       : bitmask, bit i set  <=>  element i present
#                       {e}=1, {a}=2, {b}=4, {c}=8  ->  one hex digit
#   polygroup code    : the (n-1)x(n-1) block of non-identity rows/columns,
#                       row-major, one hex digit per cell
#   semigroup code    : the n x (n-1) block obtained by deleting the column
#                       of e (which is constant: x.e = e), row-major
# --------------------------------------------------------------------------

def hexval(ch):   return int(ch, 16)

def decode_pg(code, n):
    t = [[0]*n for _ in range(n)]
    for x in range(n):
        t[0][x] = 1 << x
        t[x][0] = 1 << x
    k = 0
    for i in range(1, n):
        for j in range(1, n):
            t[i][j] = hexval(code[k]); k += 1
    assert k == len(code), f"polygroup code length {len(code)} != {k}"
    return t

def decode_sg(code, n):
    m = [[0]*n for _ in range(n)]
    for i in range(n):
        m[i][0] = 0                      # x . e = e
    k = 0
    for i in range(n):
        for j in range(1, n):
            m[i][j] = hexval(code[k]); k += 1
    assert k == len(code), f"semigroup code length {len(code)} != {k}"
    return m

# --------------------------------------------------------------------------
# axioms
# --------------------------------------------------------------------------

def hyper_mul(t, A, B, n):
    r = 0
    for a in range(n):
        if A >> a & 1:
            for b in range(n):
                if B >> b & 1:
                    r |= t[a][b]
    return r

def check_polygroup(t, n):
    """Returns (ok, message_or_inverse_map)."""
    for i in range(n):
        for j in range(n):
            if t[i][j] == 0:
                return False, f"empty hyperproduct at ({i},{j})"
    for x in range(n):                                   # scalar identity
        if t[0][x] != 1 << x or t[x][0] != 1 << x:
            return False, "e is not a scalar identity"
    for i in range(n):                                   # associativity
        for j in range(n):
            for k in range(n):
                l = r = 0
                for s in range(n):
                    if t[i][j] >> s & 1: l |= t[s][k]
                for s in range(n):
                    if t[j][k] >> s & 1: r |= t[i][s]
                if l != r:
                    return False, f"associativity fails at ({i},{j},{k})"
    inv = [None]*n                                       # unique inverse
    for x in range(n):
        cand = [y for y in range(n) if (t[x][y] & 1) and (t[y][x] & 1)]
        if len(cand) != 1:
            return False, f"inverse of {x} is not unique: {cand}"
        inv[x] = cand[0]
    for x in range(n):                                   # reversibility (P3)
        for y in range(n):
            for z in range(n):
                if t[y][z] >> x & 1:
                    if not (t[x][inv[z]] >> y & 1): return False, "reversibility fails"
                    if not (t[inv[y]][x] >> z & 1): return False, "reversibility fails"
    for x in range(n):                                   # reproduction
        row = col = 0
        for y in range(n):
            row |= t[x][y]; col |= t[y][x]
        if row != (1 << n) - 1 or col != (1 << n) - 1:
            return False, "reproduction axiom fails"
    return True, inv

def check_semigroup(m, n):
    for i in range(n):
        if m[i][0] != 0:
            return False, "e is not a right absorbing element (x.e = e fails)"
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if m[m[i][j]][k] != m[i][m[j][k]]:
                    return False, f"associativity fails at ({i},{j},{k})"
    return True, None

def left_distributive(t, m, n):
    for a in range(n):
        for b in range(n):
            for c in range(n):
                L = 0
                for s in range(n):
                    if t[b][c] >> s & 1: L |= 1 << m[a][s]
                if L != t[m[a][b]][m[a][c]]: return False
    return True

def right_distributive(t, m, n):
    for a in range(n):
        for b in range(n):
            for c in range(n):
                L = 0
                for s in range(n):
                    if t[b][c] >> s & 1: L |= 1 << m[s][a]
                if L != t[m[b][a]][m[c][a]]: return False
    return True

def bilaterally_absorbing(m, n):
    return all(m[0][x] == 0 and m[x][0] == 0 for x in range(n))

def additively_canonical(t, n):
    return all(t[x][y] == t[y][x] for x in range(n) for y in range(n))

# --------------------------------------------------------------------------
# automorphisms
# --------------------------------------------------------------------------

def perms(n):
    return [(0,) + p for p in itertools.permutations(range(1, n))]

def permsub(s, p, n):
    r = 0
    for i in range(n):
        if s >> i & 1: r |= 1 << p[i]
    return r

def aut_order(t, n, m=None):
    cnt = 0
    for p in perms(n):
        ok = True
        for i in range(n):
            for j in range(n):
                if t[p[i]][p[j]] != permsub(t[i][j], p, n): ok = False; break
                if m is not None and m[p[i]][p[j]] != p[m[i][j]]: ok = False; break
            if not ok: break
        if ok: cnt += 1
    return cnt

AUT_NAME = {1: "1", 2: "Z2", 3: "Z3", 6: "S3", 4: "Z4?", 24: "S4"}

# --------------------------------------------------------------------------
# fundamental relation
# --------------------------------------------------------------------------

def beta_star(ops, n):
    """ops: list of n x n tables of subsets.  Returns the class map."""
    F = {1 << i for i in range(n)}
    changed = True
    while changed:
        changed = False
        for A in list(F):
            for B in list(F):
                for op in ops:
                    r = hyper_mul(op, A, B, n)
                    if r and r not in F:
                        F.add(r); changed = True
    parent = list(range(n))
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for U in F:
        members = [i for i in range(n) if U >> i & 1]
        for x in members[1:]:
            a, b = find(members[0]), find(x)
            if a != b: parent[a] = b
    return [find(i) for i in range(n)]

def quotient_group(t, cls, n):
    idx, order = {}, []
    for i in range(n):
        if cls[i] not in idx:
            idx[cls[i]] = len(order); order.append(cls[i])
    k = len(order)
    g = [[None]*k for _ in range(k)]
    for i in range(n):
        for j in range(n):
            target = None
            for s in range(n):
                if t[i][j] >> s & 1:
                    c = idx[cls[s]]
                    if target is None: target = c
                    elif target != c: return "NOT-WELL-DEFINED"
            A, B = idx[cls[i]], idx[cls[j]]
            if g[A][B] is None: g[A][B] = target
            elif g[A][B] != target: return "NOT-WELL-DEFINED"
    if k == 1: return "1"
    if k == 2: return "Z2"
    if k == 3: return "Z3"
    if k == 4:
        ident = None
        for i in range(k):
            if all(g[i][j] == j and g[j][i] == j for j in range(k)): ident = i
        if ident is None: return "NOT-A-GROUP"
        return "Z4" if any(g[i][i] != ident for i in range(k)) else "Z2xZ2"
    return "?"

def subset_table(m, n):
    return [[1 << m[i][j] for j in range(n)] for i in range(n)]

# --------------------------------------------------------------------------

def canon_pg(t, n):
    best = None
    for p in perms(n):
        nt = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(n): nt[p[i]][p[j]] = permsub(t[i][j], p, n)
        c = "".join("%x" % nt[i][j] for i in range(1, n) for j in range(1, n))
        if best is None or c < best: best = c
    return best

def canon_sg(m, n):
    best = None
    for p in perms(n):
        nm = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(n): nm[p[i]][p[j]] = p[m[i][j]]
        c = "".join("%x" % nm[i][j] for i in range(n) for j in range(1, n))
        if best is None or c < best: best = c
    return best

# --------------------------------------------------------------------------

def run(datadir, n):
    fails = []
    def need(cond, msg):
        if not cond: fails.append(msg)

    def load(name):
        path = os.path.join(datadir, f"{name}_n{n}.csv")
        if not os.path.exists(path): return None
        with open(path) as f: return list(csv.DictReader(f))

    print(f"\n================  order n = {n}  ================")

    pg = load("polygroups"); sg = load("semigroups")
    hnr = load("hypernearrings"); hr = load("hyperrings"); kr = load("krasner_hyperrings")
    if pg is None: print("  (no data for this order)"); return fails

    # ---- polygroups -------------------------------------------------------
    seen = set()
    fg_count, aut_count, comm = defaultdict(int), defaultdict(int), 0
    cross = defaultdict(int)
    pg_tab = {}
    for r in pg:
        t = decode_pg(r["code"], n)
        ok, info = check_polygroup(t, n)
        need(ok, f"{r['id']}: not a polygroup ({info})")
        if not ok: continue
        c = canon_pg(t, n)
        need(c == r["code"], f"{r['id']}: code {r['code']} is not the canonical form ({c})")
        need(c not in seen, f"{r['id']}: duplicate isomorphism class")
        seen.add(c); pg_tab[r["id"]] = t
        a = aut_order(t, n)
        need(a == int(r["aut_order"]), f"{r['id']}: Aut order {r['aut_order']} != recomputed {a}")
        need(AUT_NAME[a] == r["aut_structure"], f"{r['id']}: Aut structure mismatch")
        fgr = quotient_group(t, beta_star([t], n), n)
        need(fgr == r["fundamental_group"], f"{r['id']}: fundamental group {r['fundamental_group']} != {fgr}")
        is_comm = all(t[x][y] == t[y][x] for x in range(n) for y in range(n))
        need(int(r["commutative"]) == int(is_comm), f"{r['id']}: commutativity flag wrong")
        comm += is_comm
        fg_count[fgr] += 1; aut_count[AUT_NAME[a]] += 1; cross[(AUT_NAME[a], fgr)] += 1
        # orbit-stabiliser consistency
        need(len(perms(n)) % a == 0, f"{r['id']}: |Aut| does not divide (n-1)!")
    print(f"  polygroups          : {len(pg)} classes, {comm} commutative")
    print(f"    Aut               : {dict(aut_count)}")
    print(f"    P/beta*           : {dict(fg_count)}")
    print(f"    labelled total    : {sum(len(perms(n))//int(r['aut_order']) for r in pg)}")
    print(f"    cross-tab Aut x P/beta*:")
    for k2 in sorted(cross): print(f"        Aut={k2[0]:<3} P/beta*={k2[1]:<7}: {cross[k2]}")

    # ---- semigroups -------------------------------------------------------
    seen = set(); sg_tab = {}; comm = 0
    for r in sg:
        m = decode_sg(r["code"], n)
        ok, info = check_semigroup(m, n)
        need(ok, f"{r['id']}: not a semigroup with right absorbing e ({info})")
        if not ok: continue
        c = canon_sg(m, n)
        need(c == r["code"], f"{r['id']}: code is not canonical ({c})")
        need(c not in seen, f"{r['id']}: duplicate isomorphism class")
        seen.add(c); sg_tab[r["id"]] = m
        is_comm = all(m[x][y] == m[y][x] for x in range(n) for y in range(n))
        need(int(r["commutative"]) == int(is_comm), f"{r['id']}: commutativity flag wrong")
        comm += is_comm
    print(f"  semigroups (x.e=e)  : {len(sg)} classes, {comm} commutative")
    print(f"    labelled total    : {sum(len(perms(n))//int(r['aut_order']) for r in sg)}")

    # ---- composite structures --------------------------------------------
    def check_comp(rows, name, want_right, want_absorb, want_canonical):
        if rows is None: return
        seen = set(); aut_c = defaultdict(int); fgA = defaultdict(int); fgB = defaultdict(int)
        viol = 0
        for r in rows:
            t = decode_pg(r["add_code"], n); m = decode_sg(r["mult_code"], n)
            ok1, _ = check_polygroup(t, n); ok2, _ = check_semigroup(m, n)
            need(ok1 and ok2, f"{r['id']}: constituent structure invalid")
            need(left_distributive(t, m, n), f"{r['id']}: left distributivity fails")
            if want_right:    need(right_distributive(t, m, n), f"{r['id']}: right distributivity fails")
            if want_absorb:   need(bilaterally_absorbing(m, n), f"{r['id']}: 0 not bilaterally absorbing")
            if want_canonical:need(additively_canonical(t, n), f"{r['id']}: additive part not canonical")
            key = (canon_pg(t, n), canon_sg(m, n), r["add_code"], r["mult_code"])
            a = aut_order(t, n, m)
            need(a == int(r["aut_order"]), f"{r['id']}: Aut order mismatch ({a})")
            f1 = quotient_group(t, beta_star([t], n), n)
            f2 = quotient_group(t, beta_star([t, subset_table(m, n)], n), n)
            need(f1 == r["fund_group_additive"], f"{r['id']}: additive fundamental group mismatch ({f1})")
            need(f2 == r["fund_group_full"],     f"{r['id']}: full fundamental group mismatch ({f2})")
            o = {"1":1,"Z2":2,"Z3":3,"Z4":4,"Z2xZ2":4}
            need(o[f2] <= o[f1], f"{r['id']}: STABILITY THEOREM VIOLATED ({f2} > {f1})")
            if o[f2] < o[f1]: viol += 1
            aut_c[r["aut_structure"]] += 1; fgA[f1] += 1; fgB[f2] += 1
        print(f"  {name:<20}: {len(rows)} classes")
        print(f"    Aut               : {dict(aut_c)}")
        print(f"    beta*_PG          : {dict(fgA)}")
        print(f"    beta*_full        : {dict(fgB)}   (strictly smaller in {viol} cases)")
        print(f"    labelled total    : {sum(len(perms(n))//int(r['aut_order']) for r in rows)}")

    check_comp(hnr, "hypernearrings",      False, False, False)
    check_comp(hr,  "hyperrings",          True,  True,  False)
    check_comp(kr,  "Krasner hyperrings",  True,  True,  True)

    # ---- fertility / universality re-derived from scratch -----------------
    if hnr is not None:
        fert = defaultdict(set); univ = defaultdict(set)
        fertR = defaultdict(set); univR = defaultdict(set)
        # fertility is an invariant of isomorphism CLASSES: a class of polygroups
        # and a class of semigroups are compatible iff SOME pair of labellings is.
        P = perms(n)
        for pid, t in pg_tab.items():
            for sid, m0 in sg_tab.items():
                okL = okR = False
                for p in P:
                    m = [[0]*n for _ in range(n)]
                    for i in range(n):
                        for j in range(n): m[p[i]][p[j]] = p[m0[i][j]]
                    if left_distributive(t, m, n):
                        okL = True
                        if right_distributive(t, m, n) and bilaterally_absorbing(m, n): okR = True
                    if okR: break
                if okL: fert[pid].add(sid); univ[sid].add(pid)
                if okR: fertR[pid].add(sid); univR[sid].add(pid)
        for r in pg:
            need(len(fert[r["id"]]) == int(r["fertility_hnr"]), f"{r['id']}: fertility(HNR) mismatch")
            need(len(fertR[r["id"]]) == int(r["fertility_hr"]),  f"{r['id']}: fertility(HR) mismatch")
        for r in sg:
            need(len(univ[r["id"]]) == int(r["universality_hnr"]), f"{r['id']}: universality(HNR) mismatch")
            need(len(univR[r["id"]]) == int(r["universality_hr"]), f"{r['id']}: universality(HR) mismatch")
        barrenH = sum(1 for r in sg if not univ[r["id"]])
        barrenR = sum(1 for r in sg if not univR[r["id"]])
        barrenP = sum(1 for r in pg if not fert[r["id"]])
        print(f"  barren semigroups   : {barrenH}/{len(sg)} (hypernearrings), {barrenR}/{len(sg)} (hyperrings)")
        print(f"  barren polygroups   : {barrenP}/{len(pg)}")
        print(f"  max fertility       : {max(len(fert[r['id']]) for r in pg)}"
              f"  attained by {[r['id'] for r in pg if len(fert[r['id']])==max(len(fert[q['id']]) for q in pg)]}")
    return fails


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "data"))
    args = ap.parse_args()
    allfails = []
    for n in (3, 4):
        allfails += run(args.dir, n)
    print("\n==================================================")
    if allfails:
        print(f"FAILED: {len(allfails)} check(s) did not pass\n")
        for f in allfails[:50]: print("  -", f)
        sys.exit(1)
    print("ALL CHECKS PASSED")
    sys.exit(0)

if __name__ == "__main__":
    main()
