import Mathlib.Analysis.Calculus.Deriv.Basic
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x a b : ℝ}
-- given
  (hf : deriv f x = a)
  (hg : deriv g x = b) :
-- imply
  deriv f x = a ∧ deriv g x = b := by
-- proof
  apply And.intro hf hg


-- created on 2026-10-11
