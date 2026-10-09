import Mathlib.Analysis.SpecialFunctions.PolarCoord
import sympy.Basic

open MeasureTheory


@[path]
private lemma main
  {f : ℝ × ℝ → ℝ} :
-- imply
  ∫ p : ℝ × ℝ, f p = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, p.1 * f (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
-- proof
  rw [← integral_comp_polarCoord_symm f]
  refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p _ => ?_
  rw [polarCoord_symm_apply, smul_eq_mul]


-- created on 2026-10-07
