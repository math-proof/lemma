import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a = b) :
-- imply
  Real.log a = Real.log b ∨ a = 0 :=
-- proof
  Or.inl (h ▸ rfl)


-- created on 2026-09-27
