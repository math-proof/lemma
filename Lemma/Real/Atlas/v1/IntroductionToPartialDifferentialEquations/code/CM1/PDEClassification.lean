import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.PDEClassification
open Matrix Finset PDEClassification


namespace PDEClassification

/--
[spectral_diagonalization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean)
-/
@[path]
lemma spectral_diagonalization
  [Fintype N]
  [DecidableEq N]
  {A : Matrix N N ℝ}
-- given
  (hA : A.IsHermitian) :
-- imply
  (hA.eigenvectorUnitary : Matrix N N ℝ)ᵀ * A * (hA.eigenvectorUnitary : Matrix N N ℝ) = Matrix.diagonal hA.eigenvalues := by
-- proof
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  simp only [Unitary.conjStarAlgAut_apply] at h
  have hstar_eq : star (hA.eigenvectorUnitary : Matrix N N ℝ) =
    (hA.eigenvectorUnitary : Matrix N N ℝ)ᵀ := by
    ext i j; simp [star_apply, star_trivial]
  rwa [← hstar_eq]

end PDEClassification

namespace PDEClassification

/--
[eigenvectorUnitary_det_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean)
-/
@[path]
lemma eigenvectorUnitary_det_ne_zero
  [Fintype N]
  [DecidableEq N]
  {A : Matrix N N ℝ}
-- given
  (hA : A.IsHermitian) :
-- imply
  (hA.eigenvectorUnitary : Matrix N N ℝ).det ≠ 0 := by
-- proof
  intro hdet
  have hU := (hA.eigenvectorUnitary).prop
  rw [Matrix.mem_unitaryGroup_iff'] at hU
  have h1 : (1 : Matrix N N ℝ).det = 0 := by
    rw [← hU, det_mul]
    have : star (hA.eigenvectorUnitary : Matrix N N ℝ) =
      (hA.eigenvectorUnitary : Matrix N N ℝ)ᵀ := by
      ext i j; simp [star_apply, star_trivial]
    rw [this, det_transpose, hdet, mul_zero]
  simp at h1

end PDEClassification

namespace PDEClassification

/--
[ne_zero_lt_or_gt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean)
-/
@[path]
lemma ne_zero_lt_or_gt
  [Fintype N]
  [DecidableEq N]
  {x : ℝ}
-- given
  (hx : x ≠ 0) :
-- imply
  x < 0 ∨ 0 < x := by
-- proof
  obtain h | h | h := lt_trichotomy x 0
  · exact Or.inl h
  · exact absurd h hx
  · exact Or.inr h

end PDEClassification

namespace PDEClassification

/--
[classification_normal_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean)
-/
@[path]
lemma classification_normal_form
  [Fintype N]
  [DecidableEq N]
  [Nonempty N]
  {A : Matrix N N ℝ}
-- given
  (hA : A.IsHermitian) :
-- imply
  ∃ M : Matrix N N ℝ, M.det ≠ 0 ∧ Mᵀ * A * M = Matrix.diagonal (fun i => if 0 < hA.eigenvalues i then (1 : ℝ) else if hA.eigenvalues i < 0 then (-1 : ℝ) else (0 : ℝ)) := by
-- proof
  let P : Matrix N N ℝ := hA.eigenvectorUnitary
  let scale : N → ℝ := fun i =>
    if 0 < hA.eigenvalues i then 1 / Real.sqrt (hA.eigenvalues i)
    else if hA.eigenvalues i < 0 then 1 / Real.sqrt (-(hA.eigenvalues i))
    else 1
  let S : Matrix N N ℝ := Matrix.diagonal scale
  refine ⟨P * S, ?_, ?_⟩
  ·
    rw [det_mul]
    apply mul_ne_zero (eigenvectorUnitary_det_ne_zero hA)
    rw [det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simp only [scale]
    split_ifs with h1 h2
    · exact div_ne_zero one_ne_zero (Real.sqrt_ne_zero'.mpr h1)
    · exact div_ne_zero one_ne_zero (Real.sqrt_ne_zero'.mpr (neg_pos.mpr h2))
    · exact one_ne_zero
  ·
    have key : (P * S)ᵀ * A * (P * S) = Sᵀ * (Pᵀ * A * P) * S := by
      rw [transpose_mul]; simp only [Matrix.mul_assoc]
    rw [key, spectral_diagonalization hA, diagonal_transpose]
    simp only [S]
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; ext i; simp only [scale]
    split_ifs with h1 h2
    ·
      field_simp; rw [Real.sq_sqrt (le_of_lt h1)]
    ·
      have hne : Real.sqrt (-hA.eigenvalues i) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (neg_pos.mpr h2)
      field_simp
      rw [Real.sq_sqrt (le_of_lt (neg_pos.mpr h2))]
      linarith
    ·
      push Not at h1 h2
      have h0 : hA.eigenvalues i = 0 := le_antisymm h1 h2
      simp [h0]

end PDEClassification

namespace PDEClassification

/--
[sign_diagonal_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean)
-/
@[path]
lemma sign_diagonal_eq_one
  [Fintype N]
  [DecidableEq N]
  {A : Matrix N N ℝ}
-- given
  (hA : A.IsHermitian)
  (hpos : ∀ i, 0 < hA.eigenvalues i) :
-- imply
  Matrix.diagonal (fun i => if 0 < hA.eigenvalues i then (1 : ℝ) else if hA.eigenvalues i < 0 then (-1 : ℝ) else (0 : ℝ)) = 1 := by
-- proof
  ext i j; simp only [Matrix.diagonal_apply, Matrix.one_apply]
  have hi := hpos i
  split_ifs with hij
  · subst hij; simp
  · rfl

end PDEClassification

namespace PDEClassification

/--
[sign_diagonal_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean)
-/
@[path]
lemma sign_diagonal_eq_neg_one
  [Fintype N]
  [DecidableEq N]
  {A : Matrix N N ℝ}
-- given
  (hA : A.IsHermitian)
  (hneg : ∀ i, hA.eigenvalues i < 0) :
-- imply
  Matrix.diagonal (fun i => if 0 < hA.eigenvalues i then (1 : ℝ) else if hA.eigenvalues i < 0 then (-1 : ℝ) else (0 : ℝ)) = -1 := by
-- proof
  ext i j
  have hi := hneg i
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq,
      not_lt.mpr hi.le, ite_false, hi, ite_true]
  · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.neg_apply, Matrix.one_apply_ne hij,
    neg_zero]

end PDEClassification

namespace PDEClassification

/--
[sign_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean)
-/
@[path]
lemma sign_of_ne_zero
  [Fintype N]
  [DecidableEq N]
  {A : Matrix N N ℝ}
  {i : N}
-- given
  (hA : A.IsHermitian)
  (hi : hA.eigenvalues i ≠ 0) :
-- imply
  (if 0 < hA.eigenvalues i then (1 : ℝ) else if hA.eigenvalues i < 0 then (-1 : ℝ) else (0 : ℝ)) = 1 ∨ (if 0 < hA.eigenvalues i then (1 : ℝ) else if hA.eigenvalues i < 0 then (-1 : ℝ) else (0 : ℝ)) = -1 := by
-- proof
  obtain h | h := ne_zero_lt_or_gt hi
  · simp [not_lt.mpr h.le, h]
  · simp [h]

end PDEClassification

namespace PDEClassification

/--
[classification_theorem_3_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean)
-/
@[path]
lemma classification_theorem_3_1
  [Fintype N]
  [DecidableEq N]
  [Nonempty N]
  {A : Matrix N N ℝ}
-- given
  (hA : A.IsHermitian) :
-- imply
  ∃ M : Matrix N N ℝ, M.det ≠ 0 ∧ Mᵀ * A * M = Matrix.diagonal (fun i => if 0 < hA.eigenvalues i then (1 : ℝ) else if hA.eigenvalues i < 0 then (-1 : ℝ) else (0 : ℝ)) ∧ ((IsElliptic hA → (Mᵀ * A * M = 1 ∨ Mᵀ * A * M = -1)) ∧ (IsHyperbolic hA → ∃ σ : N → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧ (∃ j, ∀ i, i ≠ j → σ i * σ j < 0) ∧ Mᵀ * A * M = Matrix.diagonal σ) ∧ (IsParabolic hA → ∃ j₀, ∃ σ : N → ℝ, σ j₀ = 0 ∧ (∀ i, i ≠ j₀ → σ i = 1 ∨ σ i = -1) ∧ (∀ i₁ i₂, i₁ ≠ j₀ → i₂ ≠ j₀ → σ i₁ = σ i₂) ∧ Mᵀ * A * M = Matrix.diagonal σ)) := by
-- proof
  obtain ⟨M, hM_det, hM_eq⟩ := classification_normal_form hA
  refine ⟨M, hM_det, hM_eq, ?_, ?_, ?_⟩
  ·
    intro hE
    obtain hpos | hneg := hE
    · exact Or.inl (hM_eq.symm ▸ sign_diagonal_eq_one hA hpos)
    · exact Or.inr (hM_eq.symm ▸ sign_diagonal_eq_neg_one hA hneg)
  ·
    intro hH
    let σ : N → ℝ := fun i =>
      if 0 < hA.eigenvalues i then (1 : ℝ)
      else if hA.eigenvalues i < 0 then (-1 : ℝ)
      else (0 : ℝ)
    refine ⟨σ, ?_, ?_, hM_eq⟩
    · intro i
      exact sign_of_ne_zero hA (hH.1 i)
    · obtain ⟨j, hj⟩ := hH.2
      refine ⟨j, fun i hi => ?_⟩
      simp only [σ]
      obtain hj_neg | hj_pos := ne_zero_lt_or_gt (hH.1 j)
      · have hi_pos : 0 < hA.eigenvalues i := by
        obtain hi_neg | hi_pos := ne_zero_lt_or_gt (hH.1 i)
        · exfalso; linarith [mul_pos_of_neg_of_neg hi_neg hj_neg, hj i hi]
        · exact hi_pos
        simp [hi_pos, not_lt.mpr hj_neg.le, hj_neg]
      · have hi_neg : hA.eigenvalues i < 0 := by
        obtain hi_neg | hi_pos := ne_zero_lt_or_gt (hH.1 i)
        · exact hi_neg
        · exfalso; linarith [mul_pos hi_pos hj_pos, hj i hi]
        simp [not_lt.mpr hi_neg.le, hi_neg, hj_pos]
  ·
    intro hP
    obtain ⟨j₀, hj₀_zero, hj₀_nonzero, hj₀_same_sign⟩ := hP
    let σ : N → ℝ := fun i =>
      if 0 < hA.eigenvalues i then (1 : ℝ)
      else if hA.eigenvalues i < 0 then (-1 : ℝ)
      else (0 : ℝ)
    refine ⟨j₀, σ, ?_, ?_, ?_, hM_eq⟩
    · simp only [σ, hj₀_zero, lt_irrefl, ↓reduceIte]
    · intro i hi
      exact sign_of_ne_zero hA (hj₀_nonzero i hi)
    · intro i₁ i₂ hi₁ hi₂; simp only [σ]
      have h_prod := hj₀_same_sign i₁ i₂ hi₁ hi₂
      obtain h1_neg | h1_pos := ne_zero_lt_or_gt (hj₀_nonzero i₁ hi₁)
      · have h2_neg : hA.eigenvalues i₂ < 0 := by
        obtain h2_neg | h2_pos := ne_zero_lt_or_gt (hj₀_nonzero i₂ hi₂)
        · exact h2_neg
        · exfalso; linarith [mul_neg_of_neg_of_pos h1_neg h2_pos]
        simp [not_lt.mpr h1_neg.le, not_lt.mpr h2_neg.le, h1_neg, h2_neg]
      · have h2_pos : 0 < hA.eigenvalues i₂ := by
        obtain h2_neg | h2_pos := ne_zero_lt_or_gt (hj₀_nonzero i₂ hi₂)
        · exfalso; linarith [mul_neg_of_pos_of_neg h1_pos h2_neg]
        · exact h2_pos
        simp [h1_pos, h2_pos]

end PDEClassification


-- created on 2026-10-23
