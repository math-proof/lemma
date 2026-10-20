import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
A standard normal has second moment `1`, the mean of the chi-squared law on one degree of freedom.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → ℝ}
-- given
  (h₀ : HasLaw x (gaussianReal 0 1) π) :
-- imply
  ∫ ω, x ω ^ 2 ∂π = 1 := by
-- proof
  have hvar : variance x π = 1 := by
    rw [← variance_id_map h₀.aemeasurable, h₀.map_eq, variance_id_gaussianReal]
    simp
  have hmean : ∫ ω, x ω ∂π = 0 := by
    simpa [integral_id_gaussianReal, Function.comp_def] using
      h₀.integral_comp (f := id) (by fun_prop)
  have hmem : MemLp x 2 π := by
    simpa [Function.comp_def] using h₀.memLp_comp (memLp_id_gaussianReal 2)
  rw [← hvar, variance_eq_sub hmem, hmean]
  simp [sub_zero]


-- created on 2021-07-18
-- updated on 2026-10-17
