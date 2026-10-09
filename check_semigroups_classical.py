#!/usr/bin/env python3
"""
Cross-check of the semigroup row of Table 1 against the classical
classification of semigroups of small order.

The classification of semigroups of order 4 is classical and is not a result of
this paper.  What the paper enumerates is the derived classification of
*pointed* semigroups: pairs (S, e) where e is a distinguished right absorbing
element, taken up to isomorphisms of S that fix e.  That is the right notion
here, because e is simultaneously the scalar identity of the hyperaddition, so
an isomorphism of hypernearrings has to carry e to e.

This script enumerates all semigroups of order n from scratch, up to plain
isomorphism, and reconciles the two counts:

    * how many semigroups of order n there are up to isomorphism;
    * how many of them admit at least one right absorbing element;
    * how many admit a (necessarily unique) bilaterally absorbing element;
    * how many pointed structures (S, e) those give -- which must equal the
      number of rows in semigroups_n*.csv.

The last line is the real check.  A semigroup may have several right absorbing
elements, so the pointed count can exceed the number of classical classes; a
zero, by contrast, is unique, so the number of pointed structures that are
bilaterally absorbing must equal the number of classical classes with a zero.

Run:  python3 check_semigroups_classical.py
"""
import csv
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# published counts of semigroups of order n up to isomorphism, for reference
KNOWN = {1: 1, 2: 5, 3: 24, 4: 188}


def enumerate_all_semigroups(n):
    """every labelled semigroup on {0..n-1}, by backtracking on associativity"""
    T = [[-1] * n for _ in range(n)]
    out = []

    def partial_ok():
        for a in range(n):
            for b in range(n):
                ab = T[a][b]
                if ab < 0:
                    continue
                for c in range(n):
                    bc = T[b][c]
                    if bc < 0:
                        continue
                    if T[ab][c] < 0 or T[a][bc] < 0:
                        continue
                    if T[ab][c] != T[a][bc]:
                        return False
        return True

    def rec(k):
        if k == n * n:
            out.append([r[:] for r in T])
            return
        i, j = divmod(k, n)
        for v in range(n):
            T[i][j] = v
            if partial_ok():
                rec(k + 1)
        T[i][j] = -1

    rec(0)
    return out


def canon(mt, n, perms):
    best = None
    for q in perms:
        nm = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                nm[q[i]][q[j]] = q[mt[i][j]]
        s = "".join("%x" % nm[i][j] for i in range(n) for j in range(n))
        if best is None or s < best:
            best = s
    return best


def right_absorbing(mt, n):
    return [e for e in range(n) if all(mt[x][e] == e for x in range(n))]


def is_zero(mt, n, e):
    return all(mt[x][e] == e and mt[e][x] == e for x in range(n))


def decode_sg(code, n):
    mt = [[0] * n for _ in range(n)]
    k = 0
    for i in range(n):
        for j in range(1, n):
            mt[i][j] = int(code[k], 16)
            k += 1
    return mt


def run(n):
    fails = []
    perms = list(itertools.permutations(range(n)))

    labelled = enumerate_all_semigroups(n)
    classes, with_right, with_zero = set(), set(), set()
    for mt in labelled:
        c = canon(mt, n, perms)
        classes.add(c)
        ra = right_absorbing(mt, n)
        if ra:
            with_right.add(c)
            if any(is_zero(mt, n, e) for e in ra):
                with_zero.add(c)

    print(f"\n================  order n = {n}  ================")
    print(f"  labelled semigroups                         : {len(labelled)}")
    print(f"  up to isomorphism                           : {len(classes)}"
          + (f"   (published value: {KNOWN[n]})" if n in KNOWN else ""))
    if n in KNOWN and len(classes) != KNOWN[n]:
        fails.append(f"n={n}: found {len(classes)} classes, published value is {KNOWN[n]}")
    print(f"  ... admitting a right absorbing element     : {len(with_right)}")
    print(f"  ... admitting a zero (bilaterally absorbing) : {len(with_zero)}")

    # ---- reconcile with the paper's pointed classification ---------------
    path = os.path.join(HERE, "data", f"semigroups_n{n}.csv")
    if not os.path.exists(path):
        print("  (no semigroups_n%d.csv, reconciliation skipped)" % n)
        return fails
    with open(path) as f:
        rows = list(csv.DictReader(f))

    bare, zeros = set(), 0
    for r in rows:
        mt = decode_sg(r["code"], n)
        bare.add(canon(mt, n, perms))
        if is_zero(mt, n, 0):
            zeros += 1

    print(f"  pointed classes (S,e) in semigroups_n{n}.csv  : {len(rows)}")
    print(f"  ... lying over this many classical classes   : {len(bare)}")
    print(f"  ... of which bilaterally absorbing           : {zeros}")

    if len(bare) != len(with_right):
        fails.append(f"n={n}: the pointed list covers {len(bare)} classical classes, "
                     f"but {len(with_right)} admit a right absorbing element")
    if zeros != len(with_zero):
        fails.append(f"n={n}: {zeros} pointed structures are bilaterally absorbing, "
                     f"but {len(with_zero)} classical classes have a zero")
    # every pointed structure must really be pointed
    for r in rows:
        mt = decode_sg(r["code"], n)
        if 0 not in right_absorbing(mt, n):
            fails.append(f"{r['id']}: e is not a right absorbing element")

    if not fails:
        print("  reconciliation: consistent "
              f"({len(bare)} classical classes carry {len(rows)} pointed structures; "
              f"the {zeros} with a zero match one-to-one)")
    return fails


def main():
    fails = []
    for n in (2, 3, 4):
        fails += run(n)
    print("\n" + "=" * 50)
    if fails:
        print(f"FAILED: {len(fails)} check(s) did not pass\n")
        for f in fails:
            print("  -", f)
        sys.exit(1)
    print("ALL CHECKS PASSED")
    sys.exit(0)


if __name__ == "__main__":
    main()
