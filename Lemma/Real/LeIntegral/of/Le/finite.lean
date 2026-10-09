import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic
import Lemma.Real.LeIntegral.of.All_Le


open MeasureTheory


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (hf : IntervalIntegrable f volume a b)
  (hg : IntervalIntegrable g volume a b)
  (h : ∀ x, f x ≤ g x) :
-- imply
  (∫ x in a..b, f x) ≤ ∫ x in a..b, g x :=
-- proof
  Real.LeIntegral.of.All_Le hab hf hg fun x _ => h x


-- created on 2019-10-31
