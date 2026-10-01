import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
-- given
  (hf : MeasureTheory.Integrable f)
  (hg : MeasureTheory.Integrable g)
  (h : ∀ x, f x ≤ g x) :
-- imply
  ∫ x, f x ≤ ∫ x, g x := by
-- proof
  exact MeasureTheory.integral_mono hf hg (fun x => h x)


@[main]
private lemma finite
  {f g : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (hf : IntervalIntegrable f MeasureTheory.volume a b)
  (hg : IntervalIntegrable g MeasureTheory.volume a b)
  (h : ∀ x, f x ≤ g x) :
-- imply
  ∫ x in a..b, f x ≤ ∫ x in a..b, g x := by
-- proof
  exact intervalIntegral.integral_mono_on hab hf hg (fun x _ => h x)


-- created on 2021-09-22
