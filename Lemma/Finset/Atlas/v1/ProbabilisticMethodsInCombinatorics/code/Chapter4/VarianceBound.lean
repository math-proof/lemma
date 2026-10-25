import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.SecondMoment
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter4.SecondMoment
open Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped Topology


namespace Thresholds

/--
[variance_isLittleO_of_deltaStar_isLittleO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/VarianceBound.lean)
-/
@[path]
lemma variance_isLittleO_of_deltaStar_isLittleO
  {μ Δstar V : ℕ → ℝ}
-- given
  (hμ_pos : ∀ᶠ n in atTop, 0 < μ n)
  (hμ_tendsto : Tendsto μ atTop atTop)
  (hΔstar_littleO : Δstar =o[atTop] μ)
  (hV_nonneg : ∀ᶠ n in atTop, 0 ≤ V n)
  (hV_bound : ∀ᶠ n in atTop, V n ≤ μ n + μ n * Δstar n) :
-- imply
  V =o[atTop] (fun n => μ n ^ 2) := by
-- proof
  have h_mul : (fun n => μ n * Δstar n) =o[atTop] (fun n => μ n ^ 2) := by
    have h := (isBigO_refl μ atTop).mul_isLittleO hΔstar_littleO
    exact h.congr_right (fun n => by ring)
  have h_lin : μ =o[atTop] (fun n => μ n ^ 2) := by
    have h_one_o_μ : (fun _ : ℕ => (1 : ℝ)) =o[atTop] μ := by
      rw [isLittleO_const_left_of_ne (one_ne_zero)]
      exact tendsto_norm_atTop_atTop.comp hμ_tendsto
    have h := h_one_o_μ.mul_isBigO (isBigO_refl μ atTop)
    exact h.congr_left (fun n => one_mul _) |>.congr_right (fun n => by ring)
  have h_sum : (fun n => μ n + μ n * Δstar n) =o[atTop] (fun n => μ n ^ 2) :=
    h_lin.add h_mul
  have h_V_O : V =O[atTop] (fun n => μ n + μ n * Δstar n) := by
    apply IsBigO.of_bound 1
    filter_upwards [hV_bound, hV_nonneg, hμ_pos] with n hVn hVnn hμn
    rw [one_mul]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    apply abs_le_abs hVn
    linarith
  exact h_V_O.trans_isLittleO h_sum

end Thresholds

namespace Thresholds

/--
[positive_whp_of_deltaStar_isLittleO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/VarianceBound.lean)
-/
@[path]
lemma positive_whp_of_deltaStar_isLittleO
  {μ Δstar V : ℕ → ℝ}
  {Ω : ℕ → Type*}
  [∀ n, MeasurableSpace (Ω n)]
  {μ_meas : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ_meas n)]
  {X : ∀ n, Ω n → ℝ}
-- given
  (hμ_pos : ∀ᶠ n in atTop, 0 < μ n)
  (hμ_tendsto : Tendsto μ atTop atTop)
  (hΔstar_littleO : Δstar =o[atTop] μ)
  (hV_nonneg : ∀ᶠ n in atTop, 0 ≤ V n)
  (hV_bound : ∀ᶠ n in atTop, V n ≤ μ n + μ n * Δstar n)
  (hX : ∀ n, MemLp (X n) 2 (μ_meas n))
  (hμ_pos_all : ∀ n, 0 < (μ_meas n)[X n])
  (hE : ∀ n, (μ_meas n)[X n] = μ n)
  (hVar_eq : ∀ n, Var[X n ; μ_meas n] = V n) :
-- imply
  Tendsto (fun n => (μ_meas n) {ω | X n ω = 0}) atTop (𝓝 0) := by
-- proof
  have hVo := variance_isLittleO_of_deltaStar_isLittleO hμ_pos hμ_tendsto hΔstar_littleO
    hV_nonneg hV_bound
  have h_ratio : Tendsto (fun n => V n / μ n ^ 2) atTop (nhds 0) :=
    hVo.tendsto_div_nhds_zero
  have h_var_ratio : Tendsto (fun n => Var[X n ; μ_meas n] / (μ_meas n)[X n] ^ 2)
    atTop (𝓝 0) := by
    have heq : (fun n => Var[X n ; μ_meas n] / (μ_meas n)[X n] ^ 2) =
      (fun n => V n / μ n ^ 2) := by
      funext n
      rw [hVar_eq, hE]
    rwa [heq]
  exact ProbabilityTheory.second_moment_method hX hμ_pos_all h_var_ratio

end Thresholds


-- created on 2026-10-23
