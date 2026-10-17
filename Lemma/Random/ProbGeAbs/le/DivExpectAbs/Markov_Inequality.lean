import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import sympy.Basic
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → ℝ}
  {a : ℝ}
-- given
  (h₀ : Integrable (fun ω => |x ω|) π)
  (h₁ : 0 < a) :
-- imply
  π.real {ω | a ≤ |x ω|} ≤ (∫ ω, |x ω| ∂π) / a :=
-- proof
  (le_div_iff₀' h₁).mpr
    (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) h₀ a)


-- created on 2023-04-18
-- updated on 2026-10-17
