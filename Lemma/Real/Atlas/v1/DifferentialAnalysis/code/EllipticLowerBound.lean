import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.EllipticLowerBound
open TemperedDistribution MvPolynomial Metric DifferentialOperators
open scoped SchwartzMap


namespace DifferentialOperators

/--
[continuous_evalPrincipalSymbolReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticLowerBound.lean)
-/
@[path]
lemma continuous_evalPrincipalSymbolReal
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ} :
-- imply
  Continuous (evalPrincipalSymbolReal m P) := by
-- proof
  show Continuous (fun ξ : Fin n → ℝ =>
    MvPolynomial.eval (fun i => (ξ i : ℂ)) (principalSymbol n m P))
  exact (MvPolynomial.continuous_eval (principalSymbol n m P)).comp
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))

end DifferentialOperators

namespace DifferentialOperators

/--
[eval_homogeneous_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticLowerBound.lean)
-/
@[path]
lemma eval_homogeneous_smul
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
  {t : ℂ}
  {ξ : Fin n → ℂ} :
-- imply
  MvPolynomial.eval (fun i => t * ξ i) (principalSymbol n m P) = t ^ m * MvPolynomial.eval ξ (principalSymbol n m P) := by
-- proof
  simp only [principalSymbol_def]
  set Q := homogeneousComponent m P with hQ_def
  have hQ_hom : Q.IsHomogeneous m := homogeneousComponent_isHomogeneous m P
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hQ_hom.degree_eq_sum_deg_support hd]
  ring

end DifferentialOperators

namespace DifferentialOperators

/--
[sphere_nonempty_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticLowerBound.lean)
-/
@[path]
lemma sphere_nonempty_of_pos
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty := by
-- proof
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact NormedSpace.sphere_nonempty.mpr (le_of_lt one_pos)

end DifferentialOperators

namespace DifferentialOperators

/--
[elliptic_lower_bound_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticLowerBound.lean)
-/
@[path]
lemma elliptic_lower_bound_sphere
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
-- given
  (hP : IsElliptic n m P)
  (hn : 0 < n) :
-- imply
  ∃ c : ℝ, 0 < c ∧ ∀ ξ : Fin n → ℝ, ‖ξ‖ = 1 → c ≤ ‖evalPrincipalSymbolReal m P ξ‖ := by
-- proof
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hne := sphere_nonempty_of_pos hn
  have hcont : ContinuousOn (fun ξ : Fin n → ℝ => ‖evalPrincipalSymbolReal m P ξ‖)
    (Metric.sphere (0 : Fin n → ℝ) 1) :=
    (continuous_norm.comp (continuous_evalPrincipalSymbolReal m P)).continuousOn
  obtain ⟨ξ₀, hξ₀_mem, hξ₀_min⟩ := hS.exists_isMinOn hne hcont
  have hξ₀_norm : ‖ξ₀‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hξ₀_mem
  have hξ₀_ne : ξ₀ ≠ 0 := by intro h; rw [h] at hξ₀_norm; simp at hξ₀_norm
  have heval_ne : evalPrincipalSymbolReal m P ξ₀ ≠ 0 := hP ξ₀ hξ₀_ne
  exact ⟨‖evalPrincipalSymbolReal m P ξ₀‖, norm_pos_iff.mpr heval_ne, fun ξ hξ =>
    hξ₀_min (by rwa [Metric.mem_sphere, dist_zero_right])⟩

end DifferentialOperators

namespace DifferentialOperators

/--
[elliptic_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticLowerBound.lean)
-/
@[path]
lemma elliptic_lower_bound
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
-- given
  (hP : IsElliptic n m P)
  (hn : 0 < n) :
-- imply
  ∃ c : ℝ, 0 < c ∧ ∀ ξ : Fin n → ℝ, c * ‖ξ‖ ^ m ≤ ‖evalPrincipalSymbolReal m P ξ‖ := by
-- proof
  obtain ⟨c, hc_pos, hc_bound⟩ := elliptic_lower_bound_sphere m P hP hn
  refine ⟨c, hc_pos, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    by_cases hm : m = 0
    ·
      subst hm
      simp only [pow_zero, mul_one]
      obtain ⟨ξ₁, hξ₁⟩ := sphere_nonempty_of_pos hn
      rw [Metric.mem_sphere, dist_zero_right] at hξ₁
      have h0 : evalPrincipalSymbolReal 0 P 0 = evalPrincipalSymbolReal 0 P ξ₁ := by
        unfold evalPrincipalSymbolReal
        have heq : (fun i : Fin n => ((0 : Fin n → ℝ) i : ℂ)) =
          (fun i => (0 : ℂ) * (ξ₁ i : ℂ)) := by ext i; simp
        rw [heq, eval_homogeneous_smul 0 P 0 (fun i => (ξ₁ i : ℂ))]
        simp
      rw [h0]; exact hc_bound ξ₁ hξ₁
    ·
      rw [norm_zero, zero_pow hm, mul_zero]; exact norm_nonneg _
  ·
    have hξ_norm_pos : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hξ_norm_ne : ‖ξ‖ ≠ 0 := ne_of_gt hξ_norm_pos
    set ξhat : Fin n → ℝ := fun i => ξ i / ‖ξ‖ with ξhat_def
    have hξhat_norm : ‖ξhat‖ = 1 := by
      have : ξhat = ‖ξ‖⁻¹ • ξ := by
        ext i; simp [ξhat_def, div_eq_mul_inv, mul_comm]
      rw [this, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hξ_norm_ne]
    have h_sphere := hc_bound ξhat hξhat_norm
    have h_homog : evalPrincipalSymbolReal m P ξ =
      (↑‖ξ‖ : ℂ) ^ m * evalPrincipalSymbolReal m P ξhat := by
      unfold evalPrincipalSymbolReal
      have htx : (fun i => (ξ i : ℂ)) = (fun i => ↑‖ξ‖ * (ξhat i : ℂ)) := by
        ext i
        simp only [ξhat_def]
        push_cast
        rw [mul_div_cancel₀ _ (by exact_mod_cast hξ_norm_ne)]
      rw [htx, eval_homogeneous_smul]
    rw [h_homog, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg ξ), mul_comm]
    exact mul_le_mul_of_nonneg_left h_sphere (pow_nonneg (norm_nonneg _) _)
end DifferentialOperators



-- created on 2026-10-23
