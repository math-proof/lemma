import Mathlib
import sympy.Basic
open Set



@[main]
private lemma main
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfc : ContinuousOn f (Icc a b))
  (hgc : ContinuousOn g (Icc a b))
  (hfg : ∀ x ∈ Ioo a b, f x > g x) :
-- imply
  (∫ x in a..b, f x) > ∫ x in a..b, g x := by
-- proof
  sorry


-- created on 2026-10-07
