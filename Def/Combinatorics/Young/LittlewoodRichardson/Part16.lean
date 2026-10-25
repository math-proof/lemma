/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Instance.Combinatorics.Young.LittlewoodRichardson.Part7
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

/-! ## Main theorems -/

/-- The minimalistic tableau T₀ of shape lam has entry i in row i.
    (Defined in the proof of thm.sf.schur-symm (b)) -/
def minimalisticTableau (lam : Fin N → ℕ) : Tableau lam zeroTuple :=
  fun c => c.val.1

/-- The set of column indices in row i with column ≥ j in the diagram lam/0.
    Used to compute contentColGeq for the minimalistic tableau. -/
def restrictedCellsRow (lam : Fin N → ℕ) (i : Fin N) (j : ℕ) : Set ℕ :=
  {k | j ≤ k ∧ 0 < k ∧ k ≤ lam i}

/-- The type of cells in column ≥ j with row index i. -/
def contentColGeqType (lam : Fin N → ℕ) (j : ℕ) (i : Fin N) :=
  {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam zeroTuple ∧ c.2 ≥ j} //
   (⟨c.val, c.prop.1⟩ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam zeroTuple}).val.1 = i}

/-- Equivalence between the content type and restricted cells. -/
def contentColGeqEquiv (lam : Fin N → ℕ) (j : ℕ) (_hj : j > 0) (i : Fin N) :
    contentColGeqType lam j i ≃ restrictedCellsRow lam i j where
  toFun := fun ⟨⟨⟨row, col⟩, hmem⟩, heq⟩ =>
    ⟨col, by
      simp only [restrictedCellsRow, Set.mem_ofPred_eq]
      simp only [skewYoungDiagram, zeroTuple, Pi.zero_apply, Set.mem_ofPred_eq] at hmem
      simp only at heq
      refine ⟨hmem.2, hmem.1.1, ?_⟩
      rw [← heq]
      exact hmem.1.2⟩
  invFun := fun ⟨k, hk⟩ =>
    ⟨⟨⟨i, k⟩, by
      simp only [skewYoungDiagram, zeroTuple, Pi.zero_apply, Set.mem_ofPred_eq]
      simp only [restrictedCellsRow, Set.mem_ofPred_eq] at hk
      exact ⟨⟨hk.2.1, hk.2.2⟩, hk.1⟩⟩, rfl⟩
  left_inv := by
    intro ⟨⟨⟨row, col⟩, hmem⟩, heq⟩
    simp only [contentColGeqType] at *
    simp only at heq
    simp only [Subtype.mk.injEq]
    ext <;> simp only [heq]
  right_inv := by
    intro ⟨k, hk⟩
    rfl

end AlgebraicCombinatorics
