import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_3
open MeasureTheory Matrix Real Finset SingularValueThresholding


namespace SingularValueThresholding

/--
[svt_term_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma svt_term_bound
  {a b τ : ℝ}
-- given
  (hτ : 0 ≤ τ)
  (hab : |a - b| ≤ τ) :
-- imply
  ((if |a| > 2 * τ then a else 0) - b) ^ 2 ≤ (if b ≠ 0 then 9 * τ ^ 2 else 0) := by
-- proof
  have hab1 : a - b ≤ τ := le_of_abs_le hab
  have hab2 : b - a ≤ τ := le_of_abs_le (by rwa [abs_sub_comm])
  by_cases hb : b = 0
  ·
    subst hb
    simp only [ne_eq, not_true_eq_false, ite_false, sub_zero] at hab ⊢
    have : ¬ (|a| > 2 * τ) := by linarith
    rw [if_neg this]; simp
  ·
    rw [if_pos hb]
    by_cases ha : |a| > 2 * τ
    ·
      rw [if_pos ha]
      nlinarith [sq_nonneg (a - b - τ), sq_nonneg (a - b + τ)]
    ·
      push_neg at ha
      rw [if_neg (by push_neg; exact ha)]
      simp only [zero_sub, neg_sq]
      have ha_upper : a ≤ 2 * τ := le_of_abs_le ha
      have ha_lower : -(2 * τ) ≤ a := by linarith [neg_abs_le a]
      nlinarith [sq_nonneg (b - 3 * τ), sq_nonneg (b + 3 * τ)]

end SingularValueThresholding

namespace SingularValueThresholding

/--
[svt_singular_value_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma svt_singular_value_bound
  {r : ℕ}
  {σ σhat : Fin r → ℝ}
  {τ : ℝ}
-- given
  (hτ : 0 ≤ τ)
  (hperturb : ∀ j, |σhat j - σ j| ≤ τ) :
-- imply
  ∑ j, ((if |σhat j| > 2 * τ then σhat j else 0) - σ j) ^ 2 ≤ 9 * (Finset.univ.filter (fun j => σ j ≠ 0)).card * τ ^ 2 := by
-- proof
  calc ∑ j, ((if |σhat j| > 2 * τ then σhat j else 0) - σ j) ^ 2
    ≤ ∑ j, (if σ j ≠ 0 then 9 * τ ^ 2 else 0) :=
    Finset.sum_le_sum (fun j _ => svt_term_bound hτ (hperturb j))
  _ = ∑ j ∈ Finset.univ.filter (fun j => σ j ≠ 0), 9 * τ ^ 2 := by
    rw [← Finset.sum_filter]
  _ = (Finset.univ.filter (fun j => σ j ≠ 0)).card • (9 * τ ^ 2) :=
    Finset.sum_const _
  _ = 9 * ↑(Finset.univ.filter (fun j => σ j ≠ 0)).card * τ ^ 2 := by
    simp [nsmul_eq_mul]; ring

end SingularValueThresholding

namespace SingularValueThresholding

/--
[theorem_4_3_svt_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma theorem_4_3_svt_bound
  {r : ℕ}
  {σ σhat : Fin r → ℝ}
  {τ : ℝ}
  {rankΘstar : ℕ}
-- given
  (hτ : 0 ≤ τ)
  (hperturb : ∀ j, |σhat j - σ j| ≤ τ)
  (hrank : (Finset.univ.filter (fun j => σ j ≠ 0)).card ≤ rankΘstar) :
-- imply
  ∑ j, ((if |σhat j| > 2 * τ then σhat j else 0) - σ j) ^ 2 ≤ 144 * ↑rankΘstar * τ ^ 2 := by
-- proof
  have h9 := svt_singular_value_bound σ σhat τ hτ hperturb
  have hn : (0 : ℝ) ≤ ↑(Finset.univ.filter (fun j => σ j ≠ 0)).card := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ ↑rankΘstar := Nat.cast_nonneg _
  have hle : (↑(Finset.univ.filter (fun j => σ j ≠ 0)).card : ℝ) ≤ ↑rankΘstar :=
    Nat.cast_le.mpr hrank
  nlinarith [sq_nonneg τ]

end SingularValueThresholding

namespace SingularValueThresholding

/--
[frobenius_norm_sq_eq_sum_entries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma frobenius_norm_sq_eq_sum_entries
  {d T : ℕ}
  {A : Matrix (Fin d) (Fin T) ℝ} :
-- imply
  ‖A‖ ^ 2 = ∑ i : Fin d, ∑ j : Fin T, A i j ^ 2 := by
-- proof
  have h1 : ‖A‖ = @norm _ (PiLp.seminormedAddCommGroup (p := 2)
    (fun _ : Fin d => PiLp 2 (fun _ : Fin T => ℝ))).toNorm
    (WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))) := rfl
  rw [h1, PiLp.norm_sq_eq_of_L2]
  congr 1; ext i; simp only []
  rw [PiLp.norm_sq_eq_of_L2]
  congr 1; ext j; simp [Real.norm_eq_abs, sq_abs]

end SingularValueThresholding

namespace SingularValueThresholding

/--
[frobenius_norm_sq_eq_sum_sq_sv_diff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma frobenius_norm_sq_eq_sum_sq_sv_diff
  {d T r : ℕ}
  {u : Fin r → (Fin d → ℝ)}
  {v : Fin r → (Fin T → ℝ)}
  {α β : Fin r → ℝ}
-- given
  (hu_ortho : ∀ i j, dotProduct (u i) (u j) = if i = j then 1 else 0)
  (hv_ortho : ∀ i j, dotProduct (v i) (v j) = if i = j then 1 else 0) :
-- imply
  frobeniusNormSq (∑ j : Fin r, α j • vecMulVec (u j) (v j) - ∑ j : Fin r, β j • vecMulVec (u j) (v j)) = ∑ j : Fin r, (α j - β j) ^ 2 := by
-- proof
  have hdiff : (∑ j : Fin r, α j • vecMulVec (u j) (v j) -
    ∑ j : Fin r, β j • vecMulVec (u j) (v j)) =
    ∑ j : Fin r, (α j - β j) • vecMulVec (u j) (v j) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext j; rw [← sub_smul]
  rw [hdiff]
  unfold frobeniusNormSq
  rw [frobenius_norm_sq_eq_sum_entries]
  have hentry : ∀ i k, (∑ j : Fin r, (α j - β j) • vecMulVec (u j) (v j)) i k =
    ∑ j : Fin r, (α j - β j) * (u j i * v j k) := by
    intro i k
    simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
  simp_rw [hentry]
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  simp_rw [show ∀ (i : Fin d) (k : Fin T) (j₁ j₂ : Fin r),
    (α j₁ - β j₁) * (u j₁ i * v j₁ k) * ((α j₂ - β j₂) * (u j₂ i * v j₂ k)) =
    (α j₁ - β j₁) * (α j₂ - β j₂) * (u j₁ i * u j₂ i) * (v j₁ k * v j₂ k)
    from fun i k j₁ j₂ => by ring]
  conv_lhs =>
    arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j₁; arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j₁; rw [Finset.sum_comm]
  have hu : ∀ j₁ j₂ : Fin r, ∑ i : Fin d, u j₁ i * u j₂ i =
    if j₁ = j₂ then 1 else 0 := by
    intro j₁ j₂; have := hu_ortho j₁ j₂; simp [dotProduct] at this; exact this
  have hv : ∀ j₁ j₂ : Fin r, ∑ k : Fin T, v j₁ k * v j₂ k =
    if j₁ = j₂ then 1 else 0 := by
    intro j₁ j₂; have := hv_ortho j₁ j₂; simp [dotProduct] at this; exact this
  have key : ∀ j₁ j₂ : Fin r, ∑ i : Fin d, ∑ k : Fin T,
    (α j₁ - β j₁) * (α j₂ - β j₂) * (u j₁ i * u j₂ i) * (v j₁ k * v j₂ k) =
    ((α j₁ - β j₁) * (α j₂ - β j₂) * if j₁ = j₂ then 1 else 0) *
      if j₁ = j₂ then 1 else 0 := by
    intro j₁ j₂
    have hfact : ∑ i : Fin d, ∑ k : Fin T,
      (α j₁ - β j₁) * (α j₂ - β j₂) * (u j₁ i * u j₂ i) * (v j₁ k * v j₂ k) =
      (α j₁ - β j₁) * (α j₂ - β j₂) * (∑ i : Fin d, u j₁ i * u j₂ i) *
        (∑ k : Fin T, v j₁ k * v j₂ k) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
    rw [hfact, hu, hv]
  simp_rw [key]
  simp only [mul_ite, mul_one, mul_zero]
  congr 1; ext x; simp

end SingularValueThresholding

namespace SingularValueThresholding

/--
[svt_frobenius_eq_sv_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma svt_frobenius_eq_sv_sum
  {d T : ℕ}
  {S_star : SVD d T}
  {S_obs : SVD d T}
  {τ : ℝ}
-- given
  (hr_eq : S_obs.r = S_star.r)
  (hu_ortho : ∀ i j : Fin S_star.r, dotProduct (S_obs.u (Fin.cast hr_eq.symm i)) (S_obs.u (Fin.cast hr_eq.symm j)) = if i = j then 1 else 0)
  (hv_ortho : ∀ i j : Fin S_star.r, dotProduct (S_obs.v (Fin.cast hr_eq.symm i)) (S_obs.v (Fin.cast hr_eq.symm j)) = if i = j then 1 else 0)
  (hstar_basis : S_star.toMatrix = ∑ j : Fin S_star.r, S_star.σval j • vecMulVec (S_obs.u (Fin.cast hr_eq.symm j)) (S_obs.v (Fin.cast hr_eq.symm j))) :
-- imply
  frobeniusNormSq (S_obs.svtMatrix τ - S_star.toMatrix) = ∑ j : Fin S_star.r, ((if |S_obs.σval (Fin.cast hr_eq.symm j)| > 2 * τ then S_obs.σval (Fin.cast hr_eq.symm j) else 0) - S_star.σval j) ^ 2 := by
-- proof
  rw [hstar_basis]
  have h_svt : S_obs.svtMatrix τ =
    ∑ j : Fin S_star.r,
      (if |S_obs.σval (Fin.cast hr_eq.symm j)| > 2 * τ
        then S_obs.σval (Fin.cast hr_eq.symm j) else 0) •
      vecMulVec (S_obs.u (Fin.cast hr_eq.symm j)) (S_obs.v (Fin.cast hr_eq.symm j)) := by
    unfold SVD.svtMatrix
    exact Fintype.sum_equiv (finCongr hr_eq) _ _
      (fun j => by simp [finCongr])
  rwa [h_svt]
    (fun j => S_obs.u (Fin.cast hr_eq.symm j))
    (fun j => S_obs.v (Fin.cast hr_eq.symm j))
    hu_ortho hv_ortho _ _

end SingularValueThresholding

namespace SingularValueThresholding

/--
[frobenius_norm_sq_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma frobenius_norm_sq_eq_sum
  {d T : ℕ}
  {A : Matrix (Fin d) (Fin T) ℝ} :
-- imply
  ‖A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
-- proof
  have h := Matrix.frobenius_norm_def A
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

end SingularValueThresholding

namespace SingularValueThresholding

/--
[ort_mulVec_norm_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma ort_mulVec_norm_sq
  {d n : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {a : Fin d → ℝ}
-- given
  (hORT : X.transpose * X = (n : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) :
-- imply
  ∑ i : Fin n, (X *ᵥ a) i ^ 2 = (n : ℝ) * ∑ k : Fin d, (a k) ^ 2 := by
-- proof
  have h1 : ∑ i : Fin n, (X *ᵥ a) i ^ 2 = dotProduct (X *ᵥ a) (X *ᵥ a) := by
    simp [dotProduct, sq]
  rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hORT]
  simp [Matrix.vecMul_smul, Matrix.vecMul_one, dotProduct, sq, Finset.mul_sum]
  ring

end SingularValueThresholding

namespace SingularValueThresholding

/--
[ort_frobenius_equality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma ort_frobenius_equality
  {d T n : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Θhat Θstar : Matrix (Fin d) (Fin T) ℝ}
-- given
  (hORT : X.transpose * X = (n : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))
  (hn : (n : ℝ) ≠ 0) :
-- imply
  (1 / (n : ℝ)) * frobeniusNormSq (X * Θhat - X * Θstar) = frobeniusNormSq (Θhat - Θstar) := by
-- proof
  unfold frobeniusNormSq
  have hfactor : X * Θhat - X * Θstar = X * (Θhat - Θstar) := by
    rw [Matrix.mul_sub]
  rw [hfactor, frobenius_norm_sq_eq_sum, frobenius_norm_sq_eq_sum]
  simp only [Matrix.mul_apply, Matrix.sub_apply]
  conv_lhs =>
    rw [show ∑ i : Fin n, ∑ j : Fin T, (∑ k, X i k * (Θhat k j - Θstar k j)) ^ 2 =
      ∑ j : Fin T, ∑ i : Fin n, (∑ k, X i k * (Θhat k j - Θstar k j)) ^ 2 from Finset.sum_comm]
  have hcol : ∀ j : Fin T,
    ∑ i : Fin n, (∑ k : Fin d, X i k * (Θhat k j - Θstar k j)) ^ 2 =
    (n : ℝ) * ∑ k : Fin d, (Θhat k j - Θstar k j) ^ 2 := by
    intro j
    have h := ort_mulVec_norm_sq X hORT (fun k => Θhat k j - Θstar k j)
    simp only [Matrix.mulVec, dotProduct] at h
    exact h
  simp_rw [hcol]
  rw [← Finset.sum_comm]
  rw [Finset.mul_sum]
  congr 1
  ext j
  rw [one_div, inv_mul_cancel_left₀ hn]

end SingularValueThresholding

namespace SingularValueThresholding

/--
[theorem_4_3_frobenius](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma theorem_4_3_frobenius
  {d T : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {model : SubGaussianMatrixModel Ω d T μ}
  {τ : ℝ}
  {S_star : SVD d T}
  {S_obs : SVD d T}
  {ω : Ω}
-- given
  (hτ : 0 ≤ τ)
  (_hS_star : S_star.IsDecompOf model.Θstar)
  (hr_eq : S_obs.r = S_star.r)
  (hWeyl : ∀ j : Fin S_star.r, |S_obs.σval (Fin.cast hr_eq.symm j) - S_star.σval j| ≤ τ)
  (hu_ortho : ∀ i j : Fin S_star.r, dotProduct (S_obs.u (Fin.cast hr_eq.symm i)) (S_obs.u (Fin.cast hr_eq.symm j)) = if i = j then 1 else 0)
  (hv_ortho : ∀ i j : Fin S_star.r, dotProduct (S_obs.v (Fin.cast hr_eq.symm i)) (S_obs.v (Fin.cast hr_eq.symm j)) = if i = j then 1 else 0)
  (hstar_basis : S_star.toMatrix = ∑ j : Fin S_star.r, S_star.σval j • vecMulVec (S_obs.u (Fin.cast hr_eq.symm j)) (S_obs.v (Fin.cast hr_eq.symm j)))
  (_hω : matrixOpNorm (model.F ω) ≤ τ)
  (_hobs : S_obs.IsDecompOf (model.observed ω)) :
-- imply
  frobeniusNormSq (S_obs.svtMatrix τ - S_star.toMatrix) ≤ 144 * (Finset.univ.filter (fun j : Fin S_star.r => S_star.σval j ≠ 0)).card * τ ^ 2 := by
-- proof
  rwa [svt_frobenius_eq_sv_sum S_star S_obs hr_eq hu_ortho hv_ortho hstar_basis τ]
    (fun j => S_star.σval j)
    (fun j => S_obs.σval (Fin.cast hr_eq.symm j))
    τ hτ hWeyl
    (Finset.univ.filter (fun j : Fin S_star.r => S_star.σval j ≠ 0)).card
    (le_refl _)

end SingularValueThresholding

namespace SingularValueThresholding

/--
[theorem_4_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean)
-/
@[path]
lemma theorem_4_3
  {d T n : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {model : SubGaussianMatrixModel Ω d T μ}
  {τ : ℝ}
  {S_star : SVD d T}
  {S_obs : SVD d T}
  {ω : Ω}
  {X : Matrix (Fin n) (Fin d) ℝ}
-- given
  (hτ : 0 ≤ τ)
  (hS_star : S_star.IsDecompOf model.Θstar)
  (hr_eq : S_obs.r = S_star.r)
  (hWeyl : ∀ j : Fin S_star.r, |S_obs.σval (Fin.cast hr_eq.symm j) - S_star.σval j| ≤ τ)
  (hu_ortho : ∀ i j : Fin S_star.r, dotProduct (S_obs.u (Fin.cast hr_eq.symm i)) (S_obs.u (Fin.cast hr_eq.symm j)) = if i = j then 1 else 0)
  (hv_ortho : ∀ i j : Fin S_star.r, dotProduct (S_obs.v (Fin.cast hr_eq.symm i)) (S_obs.v (Fin.cast hr_eq.symm j)) = if i = j then 1 else 0)
  (hstar_basis : S_star.toMatrix = ∑ j : Fin S_star.r, S_star.σval j • vecMulVec (S_obs.u (Fin.cast hr_eq.symm j)) (S_obs.v (Fin.cast hr_eq.symm j)))
  (hω : matrixOpNorm (model.F ω) ≤ τ)
  (hobs : S_obs.IsDecompOf (model.observed ω))
  (hORT : X.transpose * X = (n : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))
  (hn_pos : (0 : ℝ) < n) :
-- imply
  (1 / (n : ℝ)) * frobeniusNormSq (X * (S_obs.svtMatrix τ) - X * S_star.toMatrix) = frobeniusNormSq (S_obs.svtMatrix τ - S_star.toMatrix) ∧ frobeniusNormSq (S_obs.svtMatrix τ - S_star.toMatrix) ≤ 144 * (Finset.univ.filter (fun j : Fin S_star.r => S_star.σval j ≠ 0)).card * τ ^ 2 := by
-- proof
  constructor
  · exact ort_frobenius_equality X hORT hn_pos.ne' (S_obs.svtMatrix τ) S_star.toMatrix
  · exact theorem_4_3_frobenius model τ hτ S_star hS_star S_obs hr_eq hWeyl
    hu_ortho hv_ortho hstar_basis ω hω hobs

end SingularValueThresholding


-- created on 2026-10-23
