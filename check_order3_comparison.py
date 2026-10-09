#!/usr/bin/env python3
"""
Order-3 comparison with

    S. Borhani Nejad Rayeni and B. Davvaz,
    "On enumeration of hyper nearrings of order less than 4 and their
    automorphisms", Afrika Matematika 35, Article 59 (2024).

This script regenerates every labelled structure of order 3 from the axioms
(it does not read the CSV files, and shares no code with enumerate.cpp), and
reports the counts against the figures published in that paper.

It also reproduces the counting argument of Remark 4.3 of our paper, which
shows -- using only the figures published in [BD24] itself -- that the number
of non-isomorphic hypernearrings of order 3 cannot exceed 59.

Run:  python3 check_order3_comparison.py
"""
import itertools, sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import verify as V

n = 3
TAU = (0, 2, 1)          # the only non-identity relabelling fixing e


def perm_pg(t, p):
    nt = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            nt[p[i]][p[j]] = V.permsub(t[i][j], p, n)
    return nt


def perm_sg(x, p):
    nx = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            nx[p[i]][p[j]] = p[x[i][j]]
    return nx


def generate():
    pgs = []
    for cells in itertools.product(range(1, 8), repeat=4):
        t = [[0] * n for _ in range(n)]
        for x in range(n):
            t[0][x] = 1 << x
            t[x][0] = 1 << x
        t[1][1], t[1][2], t[2][1], t[2][2] = cells
        if V.check_polygroup(t, n)[0]:
            pgs.append(t)
    sgs = []
    for cells in itertools.product(range(n), repeat=n * (n - 1)):
        x = [[0] * n for _ in range(n)]
        k = 0
        for i in range(n):
            for j in range(1, n):
                x[i][j] = cells[k]
                k += 1
        if V.check_semigroup(x, n)[0]:
            sgs.append(x)
    hnr = [(t, x) for t in pgs for x in sgs if V.left_distributive(t, x, n)]
    return pgs, sgs, hnr


def classes(labelled, fixed):
    """orbit-counting lemma for a group of order 2"""
    return (labelled + fixed) // 2


def main():
    pgs, sgs, hnr = generate()
    fix_pg = [t for t in pgs if perm_pg(t, TAU) == t]
    fix_sg = [x for x in sgs if perm_sg(x, TAU) == x]
    fix_h = [(t, x) for (t, x) in hnr
             if perm_pg(t, TAU) == t and perm_sg(x, TAU) == x]

    rows = [
        ("quasi canonical hypergroups (polygroups)",
         len(pgs), len(fix_pg), classes(len(pgs), len(fix_pg)), 15, 10, "Lemma 3.10"),
        ("semigroups with x.e = e",
         len(sgs), len(fix_sg), classes(len(sgs), len(fix_sg)), 31, 18, "Lemma 3.11"),
        ("hypernearrings",
         len(hnr), len(fix_h), classes(len(hnr), len(fix_h)), 93, 75, "Theorem 3.12"),
    ]

    print()
    print(f"{'structure':<42}{'labelled':>9}{'tau-fix':>9}{'classes':>9}"
          f"{'[BD24] lab.':>13}{'[BD24] cl.':>12}   source")
    print("-" * 110)
    for name, lab, fx, cl, blab, bcl, src in rows:
        flag = "" if (lab == blab and cl == bcl) else "   <-- differs"
        print(f"{name:<42}{lab:>9}{fx:>9}{cl:>9}{blab:>13}{bcl:>12}   {src}{flag}")

    print()
    print("Argument of Remark 4.3, using only the figures published in [BD24]:")
    print(f"  For n = 3 the only non-identity relabelling fixing e is tau = (a b),")
    print(f"  so #classes = (#labelled + #tau-invariant) / 2.")
    print(f"  [BD24] Lemma 3.10 : 15 hypergroups in 10 classes  =>  5 are tau-invariant.")
    print(f"  [BD24] Lemma 3.11 : 31 semigroups  in 18 classes  =>  5 are tau-invariant.")
    print(f"  A hypernearring is tau-invariant iff BOTH of its tables are,")
    print(f"  so at most 5 x 5 = 25 of the 93 hypernearrings are tau-invariant, and")
    print(f"      #classes <= (93 + 25) / 2 = 59   <   75.")
    print(f"  This program finds exactly {len(fix_h)} tau-invariant hypernearrings,")
    print(f"      #classes  = (93 + {len(fix_h)}) / 2 = {classes(len(hnr), len(fix_h))}.")
    print()

    # automorphism split, to compare with Theorem 4.1 of [BD24]
    aut2 = len(fix_h)
    aut1 = classes(len(hnr), len(fix_h)) - aut2
    print(f"Automorphism groups of the {classes(len(hnr), len(fix_h))} classes "
          f"(cf. [BD24] Theorem 4.1):")
    print(f"  Aut = Z2 (self-isomorphic under tau) : {aut2}")
    print(f"  Aut = 1  (rigid)                     : {aut1}")
    print(f"  check: {aut2} x 1 + {aut1} x 2 = {aut2 + 2 * aut1}  (= 93 labelled)")
    print()

    ok = (len(pgs) == 15 and len(sgs) == 31 and len(hnr) == 93
          and classes(len(pgs), len(fix_pg)) == 10
          and classes(len(sgs), len(fix_sg)) == 18
          and classes(len(hnr), len(fix_h)) == 54
          and aut2 + 2 * aut1 == 93)
    print("ALL CHECKS PASSED" if ok else "CHECKS FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
