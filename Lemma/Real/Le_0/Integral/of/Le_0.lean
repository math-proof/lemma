import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import sympy.sets.sets
import sympy.Basic
import Lemma.Real.LeIntegral.of.All_Le


open MeasureTheory


@[main]
private lemma main
  {f : ℝ → ℝ}
  {t : ℝ}
-- given
  (ht : 0 ≤ t)
  (hf : IntervalIntegrable f volume 0 t)
  (h : ∀ x ∈ Set.Icc (0 : ℝ) t, f x ≤ 0) :
-- imply
  ∫ x in (0 : ℝ)..t, f x ≤ 0 := by
-- proof
  have hi := Real.LeIntegral.of.All_Le ht hf intervalIntegrable_const h
  rw [intervalIntegral.integral_const, sub_zero, smul_zero] at hi
  exact hi


-- created on 2023-03-25
