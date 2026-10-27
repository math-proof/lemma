import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b c t : ℝ}
  {f : ℝ → ℝ}
-- given
  (ht : 0 < t) :
-- imply
  ∫ x in a..b, f (c + t * x) * t = ∫ x in (c + t * a)..(c + t * b), f x := by
-- proof
  have h : (∫ x in a..b, f (c + t * x) * t) = ∫ x in t * a + c..t * b + c, f x := by
    rw [
      show (∫ x in a..b, f (c + t * x) * t) = ∫ x in a..b, t * f (t * x + c) by
        congr 1
        ext x
        ring_nf,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add (f := f) ht.ne' c,
      smul_eq_mul,
      mul_inv_cancel_left₀ ht.ne']
  convert h using 2 <;> ring_nf


-- created on 2026-10-10
