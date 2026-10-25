/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Instance.Combinatorics.Young.LittlewoodRichardson.Part5
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

/-- The set of columns where ν + cont(col_{≥j}(T)) fails to be a partition.

    Note: We use `maxCol + 2` in the range to ensure that `j = maxCol + 1` is included.
    This is important because for `j > maxCol`, `contentColGeq T j = 0`, so we're checking
    if `nu` itself is an N-partition. Without this, the lemma
    `violatorColumns_nonempty_of_not_yamanouchi` would fail when `nu` is not an N-partition
    but `nu + contentColGeq T j` is an N-partition for all `j ≤ maxCol`. -/
noncomputable def violatorColumns {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) : Finset ℕ :=
  let maxCol := Finset.sup Finset.univ lam
  (Finset.range (maxCol + 2)).filter (fun j => j > 0 ∧ ¬isPartitionAtColumn nu T j)

/-- Find the largest column j where ν + cont(col_{≥j}(T)) fails to be an N-partition.
    Returns `none` if T is ν-Yamanouchi (i.e., no such column exists). -/
noncomputable def findViolatorColumn {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) : Option ℕ :=
  if h : (violatorColumns nu T).Nonempty then some ((violatorColumns nu T).max' h) else none

/-- Check if index k is a misstep: α_k < α_{k+1}. -/
def isMisstep (α : Fin N → ℕ) (k : Fin N) : Prop :=
  ∃ h : k.val + 1 < N, α k < α ⟨k.val + 1, h⟩

end AlgebraicCombinatorics
