import Mathlib
import sympy.Basic

open MeasureTheory Set


@[main]
private lemma main
  {a : ℝ}
  {f : ℝ → ℝ} :
-- imply
  ∫ x, f x * (if x ≤ a then (1 : ℝ) else 0) = ∫ x in Iic a, f x := by
-- proof
  have h : (fun x => f x * (if x ≤ a then (1 : ℝ) else 0)) = (Iic a).indicator f := by
    ext x
    simp [Set.indicator]
  rw [h]
  apply integral_indicator measurableSet_Iic


-- created on 2026-10-07
