# Hyperstructures of order 4 — complete classification data

Machine-readable classification of polygroups, semigroups with a right absorbing
element, hypernearrings, hyperrings and Krasner hyperrings of order 3 and 4,
accompanying the paper

> P. Asadzadeh, M. Farshi, B. Davvaz,
> *The structure of hyper(near)rings of order 4: a computational approach to
> enumeration and classification*, Palestine Journal of Mathematics.

Everything in `data/` is produced by `src/enumerate.cpp` and is independently
re-checked, from the axioms, by `verify.py`. The two programs share no code.

---

## 1. Conventions

### 1.1 Elements

The underlying set is `R = {e, a, b, c}`, identified with `{0, 1, 2, 3}`.
For `n = 3` it is `R = {e, a, b} = {0, 1, 2}`.

`e` is simultaneously

* the **scalar identity** of the hyperaddition: `e + x = x + e = {x}`, and
* the **zero** of the multiplication.

### 1.2 Subsets as hexadecimal digits

A non-empty subset `S ⊆ R` is encoded as the bitmask `Σ_{i ∈ S} 2^i`, written as a
single hexadecimal digit.

| hex | binary | subset   | hex | binary | subset      |
|-----|--------|----------|-----|--------|-------------|
| `1` | 0001   | {e}      | `9` | 1001   | {e,c}       |
| `2` | 0010   | {a}      | `a` | 1010   | {a,c}       |
| `3` | 0011   | {e,a}    | `b` | 1011   | {e,a,c}     |
| `4` | 0100   | {b}      | `c` | 1100   | {b,c}       |
| `5` | 0101   | {e,b}    | `d` | 1101   | {e,b,c}     |
| `6` | 0110   | {a,b}    | `e` | 1110   | {a,b,c}     |
| `7` | 0111   | {e,a,b}  | `f` | 1111   | {e,a,b,c}   |
| `8` | 1000   | {c}      |     |        |             |

Bit 0 is the least significant bit and corresponds to `e`.

### 1.3 Polygroup code

The row and the column of `e` are forced by the scalar-identity axiom, so only the
`(n-1) × (n-1)` block on the non-identity elements is stored. Its cells are listed
in **row-major** order, one hex digit each:

```
a+a  a+b  a+c  b+a  b+b  b+c  c+a  c+b  c+c
```

So a polygroup of order 4 has a 9-character code and a polygroup of order 3 has a
4-character code.

**Example.** `148438887` decodes to

| `+` | e   | a   | b   | c   |
|-----|-----|-----|-----|-----|
| e   | {e} | {a} | {b} | {c} |
| a   | {a} | {e} | {b} | {c} |
| b   | {b} | {b} | {e,a} | {c} |
| c   | {c} | {c} | {c} | {e,a,b} |

(reading the code as `a+a=1`, `a+b=4`, `a+c=8`, `b+a=4`, `b+b=3`, `b+c=8`,
`c+a=8`, `c+b=8`, `c+c=7`.)

### 1.4 Semigroup code

The multiplication satisfies `x · e = e` for every `x` (see §1.5), so the column of
`e` is constant and is not stored. The remaining `n × (n-1)` cells are listed in
row-major order, each as one hex digit naming an element of `R`
(`0 = e`, `1 = a`, `2 = b`, `3 = c`):

```
e·a e·b e·c   a·a a·b a·c   b·a b·b b·c   c·a c·b c·c
```

So a semigroup of order 4 has a 12-character code.

### 1.5 The distinguished element

`e` is a **right absorbing element** of `(R, ·)`:

> `x · e = e` for every `x ∈ R`.

This is the condition imposed on the whole semigroup list. It is *not* a
multiplicative identity, and `e · x = e` is **not** assumed; the semigroups for
which `e` is in addition left absorbing (so that `0` is bilaterally absorbing, as a
Krasner hyperring requires) are exactly those whose code starts with `000`.

### 1.6 Canonical representatives

Each class is listed once, by the representative whose code is
lexicographically least over the `(n-1)!` relabellings of the non-identity
elements. For a composite structure the **same** permutation is applied to the
additive and the multiplicative table, and the pair
`add_code | mult_code` is minimised jointly; `add_code` alone is therefore not
always the canonical code of the polygroup taken on its own, and
`polygroup_id` / `semigroup_id` give the class of each constituent.

---

## 2. The classes

| file | structure |
|------|-----------|
| `polygroups_n*.csv` | polygroups: scalar identity, associativity, unique inverse, reversibility |
| `semigroups_n*.csv` | semigroups with a right absorbing element `e` |
| `hypernearrings_n*.csv` | `(R,+)` a polygroup, `(R,·)` such a semigroup, **left** distributivity |
| `hyperrings_n*.csv` | hypernearrings with `0` bilaterally absorbing and **both** distributive laws |
| `krasner_hyperrings_n*.csv` | the hyperrings whose additive part is a **canonical** hypergroup |

---

## 3. Columns

### `polygroups_n*.csv`

| column | meaning |
|--------|---------|
| `id` | `PG_k` |
| `code` | canonical polygroup code (§1.3) |
| `table` | the full `n × n` hyperaddition table, rows separated by `\|` |
| `inverse_map` | `inv(e) inv(a) inv(b) inv(c)` as digits |
| `commutative` | 1 iff `x + y = y + x` for all `x, y` |
| `aut_order`, `aut_structure` | `|Aut(P)|` and its isomorphism type |
| `fundamental_group` | `P/β*` |
| `fertility_hnr`, `fertility_hr` | `F(P)`, `F_HR(P)` (see §4) |

### `semigroups_n*.csv`

| column | meaning |
|--------|---------|
| `id`, `code`, `table`, `commutative`, `aut_order`, `aut_structure` | as above |
| `universality_hnr`, `universality_hr` | `U(S)`, `U_HR(S)` (see §4) |
| `barren_hnr`, `barren_hr` | 1 iff the corresponding universality is 0 |

### composite files

| column | meaning |
|--------|---------|
| `id` | `HNR_k`, `HR_k`, `KR_k` |
| `polygroup_id`, `semigroup_id` | the classes of the constituents |
| `add_code`, `mult_code`, `add_table`, `mult_table` | the two tables of this representative |
| `add_commutative`, `mult_commutative` | commutativity of `+` and of `·` |
| `aut_order`, `aut_structure` | automorphisms of the **composite** structure |
| `fund_group_additive` | `R/β*_{PG}`, computed from `+` alone |
| `fund_group_full` | `R/β*_{HNR}`, computed from `+` and `·` together |

---

## 4. Fertility, universality, barrenness

For an isomorphism class `[P]` of polygroups and `[S]` of semigroups, say that
they are **compatible** if *some* pair of labellings of `P` and `S` on the same
underlying set satisfies left distributivity. Compatibility depends only on the
two classes. Then

* `F(P)` = number of semigroup classes compatible with `P`;
* `U(S)` = number of polygroup classes compatible with `S`;
* `S` is **barren** if `U(S) = 0`;

and `F_HR`, `U_HR` are the same counts with "compatible" strengthened to
"forms a hyperring", i.e. `0` bilaterally absorbing and both distributive laws.

Quantifying over labellings matters: testing only the two canonical
representatives against each other undercounts (121 barren semigroups of order 4
becomes 123).

---

## 5. Reproducing everything

```
g++ -O2 -o enumerate src/enumerate.cpp     # any C++17 compiler
./enumerate 3 data
./enumerate 4 data
python3 verify.py                          # correctness   (Python 3.8+, stdlib only)
python3 enumerate_independently.py         # completeness
python3 check_order3_comparison.py         # order-3 comparison with [BD24]
python3 check_semigroups_classical.py      # reconciliation with the classical count
python3 check_hyperfields.py               # the Krasner hyperfields inside the list
```

### What each program establishes

The three programs answer different questions, and it is worth being precise
about which.

| program | language | question it answers |
|---|---|---|
| `src/enumerate.cpp` | C++17 | produces the classification |
| `verify.py` | Python 3 | **correctness** — is everything in the published list a valid structure, canonically presented, pairwise non-isomorphic, with the stated invariants? |
| `enumerate_independently.py` | Python 3 | **completeness** — is the published list the whole list? |
| `check_semigroups_classical.py` | Python 3 | **external consistency** — does the semigroup row agree with the classical classification of semigroups of order 4? |
| `check_order3_comparison.py` | Python 3 | **external consistency** — comparison with [BD24] at order 3 |
| `check_hyperfields.py` | Python 3 | extracts the Krasner hyperfields and verifies Proposition 6.11 |

`verify.py` only ever inspects structures that are already in the files, so by
construction it cannot certify that nothing is missing.
`enumerate_independently.py` closes that gap: it rebuilds every labelled
structure of orders 3 and 4 from the axioms, reads none of the CSV files,
shares no code with the C++ enumerator, recomputes the isomorphism classes, and
compares the two classifications **in both directions** — every class it
generates occurs in the published list, and every class in the published list
is generated by it. It also re-checks the labelled totals against
`Σ (n-1)!/|Aut|` and re-verifies Lemma 3.1 on every structure it produces.
All five Python programs exit non-zero on any failure.

On an ordinary laptop `enumerate` takes about a second per order,
`verify.py` about two seconds, `enumerate_independently.py` about half a
minute, and the three consistency checks about a second each. `verify.py` exits 0 only if every structure in every file satisfies its
axioms, carries the canonical code, is pairwise non-isomorphic to the others, and
has the stated automorphism group, fundamental groups, fertility and
universality. It also re-checks the inequality `|R/β*_{HNR}| ≤ |R/β*_{PG}|` on
every composite structure.

Compiler used for the published tables: `g++ (GCC) 12.2.0`, flags `-O2`,
x86-64 Linux. The enumeration is deterministic and single-threaded; no result
depends on the compiler or on the platform.

---

## 6. Summary of the classification

| | `n = 3` | `n = 4` |
|---|---|---|
| polygroups | 10 (15 labelled) | 102 (420 labelled) |
| semigroups with right absorbing `e` | 18 (31 labelled) | 151 (764 labelled) |
| hypernearrings | 54 (93 labelled) | 955 (4743 labelled) |
| hyperrings | 19 (33 labelled) | 144 (627 labelled) |
| Krasner hyperrings | 19 (33 labelled) | 139 (597 labelled) |

"Labelled" counts structures on the fixed set `R` with `e` fixed; by the
orbit–stabiliser theorem it equals `Σ (n-1)! / |Aut|` over the classes.

---

## 7. Files keyed to the paper's identifiers

`data/polygroups_n4_paperIDs.csv` and `data/semigroups_n4_paperIDs.csv` carry the
same information keyed to the identifiers `PG_1 … PG_102` and `SG_1 … SG_151`
of the supplementary material, with an extra column listing the compatible
partners by identifier.

The two schemes label the same 102 and 151 isomorphism classes, but they do not
use the same codes. The `*_n4.csv` files give each class its **canonical** code
in the sense of §1.6, that is, the lexicographically least code in the class.
The `*_paperIDs.csv` files keep the codes printed in the paper's appendix,
which are a fixed set of pairwise non-isomorphic representatives but are **not**
all canonical: 37 of the 102 polygroup codes and 45 of the 151 semigroup codes
are not the least in their class. Both files are provided so that a reader
coming from either direction can find the structure they are looking for; to
convert, canonicalise the code with the procedure in §1.6.


---

## 8. Order-3 comparison with Borhani Nejad Rayeni and Davvaz (2024)

`check_order3_comparison.py` regenerates every labelled structure of order 3
directly from the axioms — it reads none of the CSV files and shares no code
with the enumerator — and compares the result with

> S. Borhani Nejad Rayeni and B. Davvaz, *On enumeration of hyper nearrings of
> order less than 4 and their automorphisms*, Afrika Matematika **35**,
> Article 59 (2024). doi:10.1007/s13370-024-01202-8

Their Definition 2.1 is the same as ours: their *quasi canonical hypergroup* is
a polygroup in the sense of §2, and their multiplicative hypothesis is the same
condition `x · e = e` (they call `e` a left absorbing element; we follow the
standard convention and call it right absorbing — the class of semigroups is
identical).

| structure | labelled (ours) | classes (ours) | labelled [BD24] | classes [BD24] |
|---|---|---|---|---|
| quasi canonical hypergroups | 15 | 10 | 15 | 10 |
| semigroups with `x · e = e` | 31 | 18 | 31 | 18 |
| hypernearrings | 93 | **54** | 93 | **75** |

Every labelled count agrees. The isomorphism counts agree for the first two
rows but not the third, and the script prints the argument that settles it
using only the figures published in [BD24]:

For `n = 3` the only non-identity relabelling fixing `e` is `τ = (a b)`, so by
the orbit-counting lemma `#classes = (#labelled + #τ-invariant) / 2`. From
[BD24] Lemma 3.10, 15 hypergroups in 10 classes means 5 of them are
τ-invariant; from Lemma 3.11, 31 semigroups in 18 classes means 5 of those are
too. A hypernearring is τ-invariant exactly when both of its tables are, so at
most `5 × 5 = 25` of the 93 can be, giving `#classes ≤ (93 + 25)/2 = 59`, which
is already below 75. The script finds exactly 15 τ-invariant hypernearrings,
so `#classes = (93 + 15)/2 = 54`, split as 15 classes with automorphism group
`Z₂` and 39 rigid ones — the split predicted by Theorem 4.1 of [BD24].


---

## 9. Reconciliation with the classical classification of semigroups

The classification of semigroups of order 4 is classical and is not a result of
the paper. `check_semigroups_classical.py` enumerates them from scratch and
reconciles the two counts:

| | `n = 3` | `n = 4` |
|---|---|---|
| semigroups up to isomorphism | 24 | 188 |
| ... admitting a right absorbing element | 16 | 125 |
| ... admitting a zero (bilaterally absorbing) | 12 | 90 |
| **pointed** classes `(S, e)` in `semigroups_n*.csv` | **18** | **151** |
| ... lying over this many classical classes | 16 | 125 |
| ... of which bilaterally absorbing | 12 | 90 |

What the hypernearring construction needs is not a semigroup but a *pointed*
one: `e` is simultaneously the scalar identity of the hyperaddition, so an
isomorphism of hypernearrings must carry `e` to `e`, and two right absorbing
elements of the same semigroup need not be interchangeable. The objects
counted in `semigroups_n*.csv` are therefore the pairs `(S, e)` up to
isomorphisms of `S` fixing `e`, which is why 125 classical classes give rise to
151 entries.

The last row is the check that ties the two together: a zero is unique when it
exists, so each classical class with a zero must contribute exactly one pointed
structure — and 90 matches 90 at order 4, 12 matches 12 at order 3.


---

## 10. Krasner hyperfields of order 4

`check_hyperfields.py` selects, from the published list, the Krasner hyperrings
whose non-zero elements form a multiplicative group — the Krasner hyperfields.
This sub-case was classified independently by

> M. Iranmanesh, M. Jafarpour, H. Aghabozorgi, J. M. Zhan,
> *Classification of Krasner hyperfields of order 4*,
> Acta Math. Sin. (Engl. Ser.) **36**(8), 889–902 (2020).

| | `n = 3` | `n = 4` |
|---|---|---|
| Krasner hyperrings | 19 | 139 |
| ... of which Krasner hyperfields | **5** | **7** |
| ... of which are fields (single-valued `+`) | 1 (`F₃`) | 1 (`F₄`) |

At order 4 all seven share the multiplication `000123231312` (`SG_113`), whose
non-zero part is cyclic of order 3; they are distinguished by their
hyperaddition, which runs over the seven polygroups `PG_15, PG_28, PG_39,
PG_58, PG_61, PG_62, PG_65` — exactly the polygroups whose automorphism group
has order divisible by 3.

That is not a coincidence. For a Krasner hyperfield, left multiplication by a
non-zero element `g` is an automorphism of the additive polygroup (this is
left distributivity), and `g ↦ λ_g` embeds the multiplicative group into
`Aut(R, +)`. So `|R| − 1` must divide `|Aut(R, +)|`. The script verifies both
the embedding and the divisibility on every hyperfield it finds.
