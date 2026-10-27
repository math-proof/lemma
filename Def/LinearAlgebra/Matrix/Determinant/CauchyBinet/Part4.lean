/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Theorem.LinearAlgebra.Matrix.Determinant.CauchyBinet.Part2
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators
open Finset Matrix

/-!
# Determinants: Cauchy-Binet and Related Formulas

This file formalizes the Cauchy-Binet formula and related determinant identities,
following Section "Cauchy--Binet ... Factoring the matrix" of the source
(CauchyBinet.tex).

## Main definitions

* `Matrix.submatrix` - The submatrix obtained by restricting to specific rows and columns.
  This corresponds to `sub_U^V A` in the source (Definition def.det.sub).
* `colsSubmatrix`, `rowsSubmatrix` - Submatrices selecting specific columns/rows.

## Main results

* `cauchyBinet` - The general Cauchy-Binet formula for det(AB) where A is n×m and B is m×n
  (Theorem thm.det.CB)
* `cauchyBinet_square` - Special case for square matrices: det(AB) = det(A)·det(B)
* `det_mul_eq_zero_of_rank_deficient` - When m < n, det(AB) = 0
* `det_add_sum` - Formula for det(A+B) as a double sum over subsets (Theorem thm.det.det(A+B))
* `det_diagonal_submatrix_eq`, `det_diagonal_submatrix_off_diag` - Minors of diagonal matrices
  (Lemma lem.det.minors-diag)
* `det_add_diagonal` - Simplified formula when adding a diagonal matrix (Theorem thm.det.det(A+D))
* `det_const_add_diagonal` - Determinant of x + D where D is diagonal (Proposition prop.det.x+ai)
* `det_charPoly_coeff` - Coefficients of the characteristic polynomial
  (Proposition prop.det.charpol-explicit)
* `det_pascal_matrix` - The Pascal matrix has determinant 1 (Proposition prop.det.pascal-LU)

## References

* Source: CauchyBinet.tex

## Implementation notes

Mathlib already provides `Matrix.det_mul` in `Mathlib.LinearAlgebra.Matrix.Determinant`.
We provide additional results and connect Mathlib's API to the textbook presentation.

The submatrix operation `Matrix.submatrix` uses functions for row/column selection,
which is more general than the textbook's subset-based notation.
-/


namespace AlgebraicCombinatorics

namespace CauchyBinet

variable {R : Type*} [CommRing R]

/-- Extract α from σ: For σ with σ(P) = Q, extract the permutation α ∈ Perm(Fin |P|)
    that describes how σ permutes the elements of P.
    
    Specifically, if p₁ < p₂ < ... < pₖ are the elements of P and 
    q₁ < q₂ < ... < qₖ are the elements of Q, then α is defined by
    σ(pᵢ) = q_{α(i)}. -/
noncomputable def extractAlpha {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) : Equiv.Perm (Fin P.card) := by
  let pEmb := P.orderEmbOfFin rfl
  have h : ∀ i : Fin P.card, σ (pEmb i) ∈ Q := sigma_orderEmb_mem_of_imageFinset P Q σ hσ
  let qIso : Fin P.card ≃o Q := Q.orderIsoOfFin hcard.symm
  let f : Fin P.card → Fin P.card := fun i => qIso.symm ⟨σ (pEmb i), h i⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    have := qIso.symm.injective hab
    simp only [Subtype.mk.injEq] at this
    exact pEmb.injective (σ.injective this)
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- Extract β from σ: For σ with σ(P) = Q, extract the permutation β ∈ Perm(Fin |Pᶜ|)
    that describes how σ permutes the elements of Pᶜ. -/
noncomputable def extractBeta {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) : Equiv.Perm (Fin Pᶜ.card) := by
  have hcard' : Pᶜ.card = Qᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, hcard]
  let pEmb := Pᶜ.orderEmbOfFin rfl
  have h : ∀ i : Fin Pᶜ.card, σ (pEmb i) ∈ Qᶜ := sigma_orderEmb_compl_mem_of_imageFinset P Q σ hσ
  let qIso : Fin Pᶜ.card ≃o (Qᶜ : Finset (Fin n)) := Qᶜ.orderIsoOfFin hcard'.symm
  let f : Fin Pᶜ.card → Fin Pᶜ.card := fun i => qIso.symm ⟨σ (pEmb i), h i⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    have := qIso.symm.injective hab
    simp only [Subtype.mk.injEq] at this
    exact pEmb.injective (σ.injective this)
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-! ### Helper lemmas for empty set case in sign_decomposition -/

/-- Given α ∈ Perm(Fin |P|) and β ∈ Perm(Fin |Pᶜ|), construct σ ∈ Perm(Fin n) with σ(P) = Q.
    This is the inverse of the (extractAlpha, extractBeta) bijection. -/
noncomputable def constructSigma {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (α : Equiv.Perm (Fin P.card)) (β : Equiv.Perm (Fin Pᶜ.card)) : Equiv.Perm (Fin n) := by
  have hcardC : Pᶜ.card = Qᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, hcard]
  let pEmb := P.orderEmbOfFin rfl
  let qEmb : Fin P.card ↪o Fin n := Q.orderEmbOfFin (by rw [hcard])
  let pCEmb := Pᶜ.orderEmbOfFin rfl
  let qCEmb : Fin Pᶜ.card ↪o Fin n := Qᶜ.orderEmbOfFin (by rw [hcardC])
  -- Construct the function
  let f : Fin n → Fin n := fun x =>
    if h : x ∈ P then
      qEmb (α ((P.orderIsoOfFin rfl).symm ⟨x, h⟩))
    else
      qCEmb (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨x, Finset.mem_compl.mpr h⟩))
  -- Prove it's a bijection
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    by_cases ha : a ∈ P <;> by_cases hb : b ∈ P
    · simp only [ha, hb, dif_pos] at hab
      have := qEmb.injective hab
      have := α.injective this
      have := (P.orderIsoOfFin rfl).symm.injective this
      simp only [Subtype.mk.injEq] at this
      exact this
    · simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true] at hab
      have h1 : qEmb (α ((P.orderIsoOfFin rfl).symm ⟨a, ha⟩)) ∈ Q := Finset.orderEmbOfFin_mem _ _ _
      have h2 : qCEmb (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨b, Finset.mem_compl.mpr hb⟩)) ∈ Qᶜ := 
        Finset.orderEmbOfFin_mem _ _ _
      rw [hab] at h1
      exact absurd h1 (Finset.mem_compl.mp h2)
    · simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true] at hab
      have h1 : qEmb (α ((P.orderIsoOfFin rfl).symm ⟨b, hb⟩)) ∈ Q := Finset.orderEmbOfFin_mem _ _ _
      have h2 : qCEmb (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨a, Finset.mem_compl.mpr ha⟩)) ∈ Qᶜ := 
        Finset.orderEmbOfFin_mem _ _ _
      rw [← hab] at h1
      exact absurd h1 (Finset.mem_compl.mp h2)
    · simp only [ha, hb, dif_neg, not_false_eq_true] at hab
      have := qCEmb.injective hab
      have := β.injective this
      have := (Pᶜ.orderIsoOfFin rfl).symm.injective this
      simp only [Subtype.mk.injEq] at this
      exact this
  exact Equiv.ofBijective f ⟨hf_inj, Finite.injective_iff_surjective.mp hf_inj⟩

/-! ### Base case lemmas for sign decomposition using subtypePerm

When P = Q = {0, 1, ..., k-1} (the first k elements), the sign identity simplifies
because inversions split cleanly into three categories:
1. Inversions within P (counted by α)
2. Inversions within Pᶜ (counted by β)  
3. Inversions between P and Pᶜ (which are zero because σ preserves both sets)

We formalize this using Mathlib's `sign_subtypeCongr` lemma and `Equiv.Perm.subtypePerm`.
-/


/-- Predicate for "i.val < k" used to partition Fin n. -/
def ltPred (n k : ℕ) : Fin n → Prop := fun i => i.val < k

end CauchyBinet
end AlgebraicCombinatorics
