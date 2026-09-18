import Mathlib.Analysis.Calculus.Deriv.Basic
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ} {f' g' x : ℝ}
-- given
  (hfg : f = g)
  (hfg' : f' = g')
  (h : HasDerivAt f f' x) :
-- imply
  HasDerivAt g g' x := by
-- proof
  aesop


-- created on 2026-09-18
