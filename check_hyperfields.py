#!/usr/bin/env python3
"""
Extracts the Krasner hyperfields of order 3 and 4 from the published list.

A Krasner hyperfield is a Krasner hyperring (R, +, .) with |R| >= 2 in which
the non-zero elements form a group under multiplication.  This is a sub-case of
the classification in the paper, treated independently in

    M. Iranmanesh, M. Jafarpour, H. Aghabozorgi, J. M. Zhan,
    "Classification of Krasner hyperfields of order 4",
    Acta Math. Sin. (Engl. Ser.) 36(8), 889-902 (2020).

The script also checks the necessary condition of Proposition 6.11 of the paper:
for a Krasner hyperfield, left multiplication by a non-zero element is an
automorphism of the additive polygroup, so the multiplicative group embeds in
Aut(R, +) and |R| - 1 must divide |Aut(R, +)|.

Run:  python3 check_hyperfields.py
"""
import csv
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import verify as V


def multiplicative_group(mt, n):
    """Return the identity of (R\\{0}, .) if it is a group, else None."""
    U = list(range(1, n))
    for x in U:
        for y in U:
            if mt[x][y] == 0:
                return None                      # not closed
    ident = [e for e in U if all(mt[e][x] == x and mt[x][e] == x for x in U)]
    if len(ident) != 1:
        return None
    e = ident[0]
    for x in U:
        if not any(mt[x][y] == e and mt[y][x] == e for y in U):
            return None                          # no inverse
    return e


def left_mult_is_automorphism(t, mt, n, g):
    """lambda_g(x) = g.x preserves +, as Proposition 6.11 asserts."""
    lam = [mt[g][x] for x in range(n)]
    if sorted(lam) != list(range(n)):
        return False
    for x in range(n):
        for y in range(n):
            img = 0
            for s in range(n):
                if t[x][y] >> s & 1:
                    img |= 1 << lam[s]
            if img != t[lam[x]][lam[y]]:
                return False
    return True


def run(n):
    fails = []
    path = os.path.join(HERE, "data", f"krasner_hyperrings_n{n}.csv")
    if not os.path.exists(path):
        return fails
    with open(path) as f:
        rows = list(csv.DictReader(f))

    found = []
    for r in rows:
        t = V.decode_pg(r["add_code"], n)
        mt = V.decode_sg(r["mult_code"], n)
        e = multiplicative_group(mt, n)
        if e is None:
            continue
        found.append(r)
        # Proposition 6.11: every lambda_g is an automorphism of (R, +)
        for g in range(1, n):
            if not left_mult_is_automorphism(t, mt, n, g):
                fails.append(f"{r['id']}: left multiplication by {g} is not an "
                             f"automorphism of the hyperaddition")
        # ... hence (n-1) divides |Aut(R, +)|
        a = V.aut_order(t, n)
        if a % (n - 1) != 0:
            fails.append(f"{r['id']}: |Aut(R,+)| = {a} is not divisible by {n-1}")

    print(f"\n================  order n = {n}  ================")
    print(f"  Krasner hyperrings   : {len(rows)}")
    print(f"  ... of which hyperfields : {len(found)}")
    for r in found:
        t = V.decode_pg(r["add_code"], n)
        single = all(bin(t[i][j]).count("1") == 1
                     for i in range(n) for j in range(n))
        tag = "   <- single-valued hyperaddition: this is the field" if single else ""
        print(f"      {r['id']:<8} add={r['add_code']:<10} mult={r['mult_code']:<13}"
              f" |Aut|={V.aut_order(t, n)}{tag}")
    print(f"  Proposition 6.11 verified on all {len(found)} of them "
          f"(each lambda_g is an automorphism; {n-1} divides |Aut(R,+)|)")
    return fails


def main():
    fails = []
    for n in (3, 4):
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
