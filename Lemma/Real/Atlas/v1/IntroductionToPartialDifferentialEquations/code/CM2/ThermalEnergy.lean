import Mathlib
import sympy.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM2.ThermalEnergy
open MeasureTheory Filter HeatEquation


namespace HeatEquation

/--
[integral_laplacian_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/ThermalEnergy.lean)
-/
@[path]
lemma integral_laplacian_eq_zero
  {n : ℕ}
  {laplacian_u : ℝ → (Fin n → ℝ) → ℝ}
  {grad_u_norm : ℝ → (Fin n → ℝ) → ℝ}
  {t : ℝ}
-- given
  (hdecay : ∀ t, Tendsto (fun (R : ℝ) => sSup ((fun x => R ^ ((n : ℝ) - 1) * |grad_u_norm t x|) '' (Metric.sphere (0 : Fin n → ℝ) R))) atTop (nhds 0))
  (hlapl_int : ∀ t, Integrable (laplacian_u t))
  (hdiv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t R, 0 < R → |∫ x in Metric.ball (0 : Fin n → ℝ) R, laplacian_u t x| ≤ C * sSup ((fun x => R ^ ((n : ℝ) - 1) * |grad_u_norm t x|) '' Metric.sphere (0 : Fin n → ℝ) R)) :
-- imply
  ∫ x : Fin n → ℝ, laplacian_u t x = 0 := by
-- proof
  obtain ⟨C, hC_nn, hbound⟩ := hdiv_bound
  have hcover : AECover (volume : Measure (Fin n → ℝ)) atTop
    (fun R : ℝ => Metric.ball (0 : Fin n → ℝ) R) :=
    MeasureTheory.aecover_ball tendsto_id
  have htend : Tendsto (fun R => ∫ x in Metric.ball (0 : Fin n → ℝ) R, laplacian_u t x)
    atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero'
    · filter_upwards with R; exact abs_nonneg _
    · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with R hR; exact hbound t R hR
    · rw [show (0 : ℝ) = C * 0 from by ring]; exact (hdecay t).const_mul C
  exact hcover.integral_eq_of_tendsto 0 (hlapl_int t) htend
/-- For a solution $u$ to the heat equation $\partial_t u = \Delta u$ on $\mathbb{R}^n$
with suitable decay and integrability hypotheses, the derivative of the total thermal
energy with respect to time vanishes: $\mathcal{T}'(t) = 0$. This is the differential
form of conservation of thermal energy (Lemma 2.0.3). -/

end HeatEquation


-- created on 2026-10-23
