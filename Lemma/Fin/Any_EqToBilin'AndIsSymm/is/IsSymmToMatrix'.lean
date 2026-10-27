import Mathlib
import Initialize.Tactic.Attr.Basic
open LinearMap LinearMap.BilinForm Module


/--
[bilinearForm_matrix_correspondence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/BilinearForms.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {B : LinearMap.BilinForm ℝ (Fin n → ℝ)} :
-- imply
  (∃ A : Matrix (Fin n) (Fin n) ℝ, Matrix.toBilin' A = B) ∧ (LinearMap.IsSymm B ↔ (BilinForm.toMatrix' B).IsSymm) := by
-- proof
  constructor
  · exact ⟨BilinForm.toMatrix' B, Matrix.toBilin'_toMatrix' B⟩
  · constructor
    · intro h
      ext i j
      simp only [Matrix.transpose_apply, BilinForm.toMatrix'_apply]
      exact h.eq _ _
    · intro h
      constructor
      intro x y
      simp only [RingHom.id_apply]
      conv_lhs => rw [← Matrix.toBilin'_toMatrix' B]
      conv_rhs => rw [← Matrix.toBilin'_toMatrix' B]
      simp only [Matrix.toBilin'_apply]
      rw [Finset.sum_comm]
      congr 1
      ext i
      congr 1
      ext j
      have hM := h.apply i j
      rw [hM]
      ring



/--
[orthogonal_complement_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/BilinearForms.lean)
-/
private lemma orthogonal_complement_def
  [CommSemiring R]
  [AddCommMonoid M]
  [Module R M]
  {B : LinearMap.BilinForm R M}
  {W : Submodule R M}
  {v : M} :
-- imply
  v ∈ B.orthogonal W ↔ ∀ w ∈ W, B.IsOrtho w v :=
-- proof
  mem_orthogonal_iff



/--
[nondegenerate_iff_det_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/BilinearForms.lean)
-/
private lemma nondegenerate_iff_det_ne_zero
  [CommRing A]
  [IsDomain A]
  [AddCommGroup M]
  [Module A M]
  [DecidableEq ι]
  [Fintype ι]
  {B : LinearMap.BilinForm A M}
  {b : Basis ι A M} :
-- imply
  B.Nondegenerate ↔ (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
-- proof
  LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b



/--
[exists_normalized_orthogonal_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/BilinearForms.lean)
-/
private lemma exists_normalized_orthogonal_basis
  [AddCommGroup M]
  [Module ℝ M]
  [FiniteDimensional ℝ M]
  {Q : QuadraticForm ℝ M} :
-- imply
  ∃ w : Fin (finrank ℝ M) → ℝ, (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w) :=
-- proof
  QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared Q



/--
[signature_invariance](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/BilinearForms.lean)
-/
private lemma signature_invariance
  [AddCommGroup M]
  [Module ℝ M]
  {Q Q' : QuadraticForm ℝ M}
-- given
  (h : QuadraticMap.Equivalent Q Q') :
-- imply
  sigPos Q = sigPos Q' ∧ sigNeg Q = sigNeg Q' ∧ (finrank ℝ M - sigPos Q - sigNeg Q = finrank ℝ M - sigPos Q' - sigNeg Q') := by
-- proof
  exact ⟨h.sigPos_eq, h.sigNeg_eq, by rw [h.sigPos_eq, h.sigNeg_eq]⟩



-- created on 2026-10-23
-- updated on 2026-10-26
