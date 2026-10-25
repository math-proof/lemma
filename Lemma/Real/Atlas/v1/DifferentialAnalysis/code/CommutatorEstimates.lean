import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.CommutatorEstimates
open TemperedDistribution MvPolynomial DifferentialOperators
open scoped SchwartzMap


namespace DifferentialOperators

/--
[parametrixSymbol_eq_zero_near_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CommutatorEstimates.lean)
-/
@[path]
lemma parametrixSymbol_eq_zero_near_zero
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
  {φ : SmoothCutoff n}
  {ξ : Fin n → ℝ}
-- given
  (hξ : ‖ξ‖ ≤ 1) :
-- imply
  parametrixSymbol m P φ ξ = 0 := by
-- proof
  unfold parametrixSymbol
  have hφ : φ.toFun ξ = 1 := φ.eq_one_near_zero ξ hξ
  split_ifs with h
  · rfl
  · simp [hφ]

end DifferentialOperators

namespace DifferentialOperators

/--
[parametrixSymbol_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CommutatorEstimates.lean)
-/
@[path]
lemma parametrixSymbol_bound
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
  {φ : SmoothCutoff n}
-- given
  (hP : IsElliptic n m P)
  (hn : 0 < n) :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ ξ : Fin n → ℝ, ‖parametrixSymbol m P φ ξ‖ ≤ C / ‖ξ‖ ^ m := by
-- proof
  obtain ⟨c, hc_pos, hc_bound⟩ := elliptic_lower_bound m P hP hn
  refine ⟨c⁻¹, inv_pos.mpr hc_pos, fun ξ => ?_⟩
  by_cases hξ_small : ‖ξ‖ ≤ 1
  · rw [parametrixSymbol_eq_zero_near_zero m P φ ξ hξ_small, norm_zero]
    positivity
  · have hξ_large : 1 < ‖ξ‖ := not_le.mp hξ_small
    have hξ_pos : 0 < ‖ξ‖ := by linarith
    have hξ_ne : ξ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hξ_pos)
    have hPm_ne : evalPrincipalSymbolReal m P ξ ≠ 0 := hP ξ hξ_ne
    have hQ : parametrixSymbol m P φ ξ =
      (1 - (φ.toFun ξ : ℂ)) / evalPrincipalSymbolReal m P ξ := by
      unfold parametrixSymbol; rw [if_neg hPm_ne]
    rw [hQ, norm_div]
    have hPm_pos : 0 < ‖evalPrincipalSymbolReal m P ξ‖ := norm_pos_iff.mpr hPm_ne
    rw [div_le_div_iff₀ hPm_pos (pow_pos hξ_pos m)]
    have hnum_le : ‖(1 : ℂ) - (φ.toFun ξ : ℂ)‖ ≤ 1 := by
      have h1 : (1 : ℂ) - (φ.toFun ξ : ℂ) = ((1 - φ.toFun ξ : ℝ) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_of_nonneg (by linarith [φ.le_one ξ])]
      linarith [φ.nonneg ξ]
    calc ‖(1 : ℂ) - (φ.toFun ξ : ℂ)‖ * ‖ξ‖ ^ m
      ≤ 1 * ‖ξ‖ ^ m :=
        mul_le_mul_of_nonneg_right hnum_le (pow_nonneg (norm_nonneg _) _)
      _ = ‖ξ‖ ^ m := one_mul _
      _ = c⁻¹ * (c * ‖ξ‖ ^ m) :=
        (inv_mul_cancel_left₀ (ne_of_gt hc_pos) _).symm
      _ ≤ c⁻¹ * ‖evalPrincipalSymbolReal m P ξ‖ :=
        mul_le_mul_of_nonneg_left (hc_bound ξ) (le_of_lt (inv_pos.mpr hc_pos))

end DifferentialOperators

namespace DifferentialOperators

/--
[continuous_parametrixSymbol](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CommutatorEstimates.lean)
-/
@[path]
lemma continuous_parametrixSymbol
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
  {φ : SmoothCutoff n}
-- given
  (hP : IsElliptic n m P) :
-- imply
  Continuous (parametrixSymbol m P φ) := by
-- proof
  rw [continuous_iff_continuousAt]
  intro ξ₀
  by_cases hξ₀ : ‖ξ₀‖ < 1
  ·
    have : parametrixSymbol m P φ =ᶠ[nhds ξ₀] fun _ => (0 : ℂ) := by
      apply Filter.eventually_of_mem
        (Metric.ball_mem_nhds ξ₀ (show 0 < 1 - ‖ξ₀‖ by linarith))
      intro ξ hξ
      rw [Metric.mem_ball] at hξ
      exact parametrixSymbol_eq_zero_near_zero m P φ ξ
        (by linarith [dist_eq_norm ξ ξ₀, norm_sub_norm_le ξ ξ₀])
    exact continuousAt_const.congr this.symm
  ·
    push_neg at hξ₀
    have hξ₀_ne : ξ₀ ≠ 0 := by
      intro h; subst h; simp at hξ₀; linarith
    have hPm_ne : evalPrincipalSymbolReal m P ξ₀ ≠ 0 := hP ξ₀ hξ₀_ne
    have hev : parametrixSymbol m P φ =ᶠ[nhds ξ₀]
      (fun ξ => (1 - (φ.toFun ξ : ℂ)) / evalPrincipalSymbolReal m P ξ) := by
      apply Filter.eventually_of_mem
        ((continuous_evalPrincipalSymbolReal m P).isOpen_preimage {0}ᶜ isOpen_compl_singleton
          |>.mem_nhds (by simp [hPm_ne]))
      intro ξ hξ
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hξ
      simp only [parametrixSymbol, if_neg hξ]
    have hnum_cont : Continuous (fun ξ => (1 : ℂ) - (φ.toFun ξ : ℂ)) :=
      continuous_const.sub (Complex.continuous_ofReal.comp φ.continuous_toFun)
    exact (hnum_cont.continuousAt.div
      (continuous_evalPrincipalSymbolReal m P).continuousAt hPm_ne).congr hev.symm

end DifferentialOperators

namespace DifferentialOperators

/--
[parametrixSymbol_polynomial_decay](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CommutatorEstimates.lean)
-/
@[path]
lemma parametrixSymbol_polynomial_decay
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
  {φ : SmoothCutoff n}
-- given
  (hP : IsElliptic n m P)
  (hn : 0 < n) :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ ξ : Fin n → ℝ, ‖parametrixSymbol m P φ ξ‖ ≤ C * (1 + ‖ξ‖)⁻¹ ^ m := by
-- proof
  obtain ⟨C, hC_pos, hC_bound⟩ := parametrixSymbol_bound m P φ hP hn
  refine ⟨C * 2 ^ m, by positivity, fun ξ => ?_⟩
  by_cases hξ_small : ‖ξ‖ ≤ 1
  · rw [parametrixSymbol_eq_zero_near_zero m P φ ξ hξ_small, norm_zero]
    positivity
  · push_neg at hξ_small
    have hξ_pos : 0 < ‖ξ‖ := by linarith
    calc ‖parametrixSymbol m P φ ξ‖
      ≤ C / ‖ξ‖ ^ m := hC_bound ξ
      _ = C * (‖ξ‖⁻¹ ^ m) := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ C * (2 * (1 + ‖ξ‖)⁻¹) ^ m := by
        gcongr
        rw [inv_le_comm₀ hξ_pos (by positivity)]
        rw [mul_inv_rev, inv_inv]
        linarith
      _ = C * 2 ^ m * (1 + ‖ξ‖)⁻¹ ^ m := by rw [mul_pow, mul_assoc]

end DifferentialOperators

namespace DifferentialOperators

/--
[elliptic_parametrix_construction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CommutatorEstimates.lean)
-/
@[path]
lemma elliptic_parametrix_construction
  {n : ℕ}
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
-- given
  (hP : IsElliptic n m P) :
-- imply
  ∃ (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)), IsParametrix P F ∧ singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))} :=
-- proof
  parametrix_exists_with_singSupp hP
end DifferentialOperators



-- created on 2026-10-23
