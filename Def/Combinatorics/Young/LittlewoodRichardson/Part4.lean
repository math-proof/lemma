/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Abbrev.Combinatorics.Young.LittlewoodRichardson.Part2
open Finset Function BigOperators Polynomial MvPolynomial

/-!
# The Littlewood-Richardson Rule

This file formalizes the Littlewood-Richardson rule for Schur polynomials, following
the presentation in the Algebraic Combinatorics textbook.

The Littlewood-Richardson rule is one of the most famous results in the theory of symmetric
polynomials. It provides a combinatorial formula for expanding the product of Schur polynomials
as a sum of Schur polynomials:
$$s_\nu \cdot s_{\lambda/\mu} = \sum_{T} s_{\nu + \operatorname{cont}(T)}$$
where the sum is over all ν-Yamanouchi semistandard tableaux T of shape λ/μ.

## Main definitions

* `NPartition`: An N-partition is a weakly decreasing N-tuple of natural numbers
* `contentTableau`: The content of a tableau (counting occurrences of each entry)
* `colGeq`: Restriction of a tableau to columns ≥ j
* `IsYamanouchi`: A semistandard tableau is ν-Yamanouchi if certain conditions hold
* `alternant`: The alternant polynomial a_α
* `schurPoly`: The Schur polynomial s_λ (via the Jacobi-Trudi formula)
* `skewSchurPoly`: The skew Schur polynomial s_{λ/μ}

## Main results

* `littlewoodRichardson`: Zelevinsky's generalized Littlewood-Richardson rule (thm.sf.lr-zy)
* `stembridgeLemma`: Stembridge's lemma (lem.sf.stemb-lem)
* `schurPoly_eq_alternant_div`: Theorem relating Schur polynomials to alternants (thm.sf.schur-symm (b))

## Indexing Convention

**This file uses 1-indexed columns** for skew Young diagrams, matching the textbook convention:
- A cell (i, j) is in Y(λ/μ) iff μ_i < j ≤ λ_i
- Column indices start at 1 (the first column is j = 1)

This differs from `SchurBasics.lean` which uses **0-indexed columns** (Mathlib convention):
- A cell (i, j) is in Y(λ/μ) iff μ_i ≤ j < λ_i
- Column indices start at 0 (the first column is j = 0)

The bijection (i, j) ↔ (i, j+1) converts between the conventions.
See `SchurBasics.skewCellEquiv` and `SchurBasics.mem_skewYoungDiagram_iff_mem_LR_shifted`
for explicit equivalences.

## References

* [Stembridge, *A concise proof of the Littlewood-Richardson rule*][Stembr02]
* [Grinberg-Reiner, *Hopf algebras in Combinatorics*][GriRei]

## Tags

Littlewood-Richardson rule, Schur polynomial, Yamanouchi tableau, symmetric polynomial
-/


namespace AlgebraicCombinatorics

variable {R : Type*} [CommRing R]

variable {N : ℕ}

/-! ## Column restriction of tableaux (def.sf.col-tab)

**Definition (def.sf.col-tab)**: Let λ and μ be two N-partitions. Let T be a tableau of shape λ/μ.
Let j be a positive integer. Then, col_{≥j}(T) means the restriction of T to columns j, j+1, j+2, ...
(that is, the result of removing the first j-1 columns from T).

Formally speaking, this means the restriction of the map T to the set {(u,v) ∈ Y(λ/μ) | v ≥ j}.

**Note**: col_{≥1}(T) = T for any tableau T. -/


/-- The restriction of a tableau to columns ≥ j. (def.sf.col-tab)

    For a tableau T of shape λ/μ, `colGeq T j` is the restriction of T to the cells
    in columns j, j+1, j+2, ... This is the formal definition of col_{≥j}(T).

    The domain is {(u,v) ∈ Y(λ/μ) | v ≥ j}, and the function returns T(u,v)
    for each such cell. -/
def colGeq {lam mu : Fin N → ℕ} (T : Tableau lam mu) (j : ℕ) :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} → Fin N :=
  fun ⟨c, hc⟩ => T ⟨c, hc.1⟩

end AlgebraicCombinatorics
