import Mathlib.Analysis.Calculus.Deriv.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ} {f' x : ℝ}
-- given
  (hfg : f = g)
  (h : HasDerivAt f f' x) :
-- imply
  HasDerivAt g f' x := by
-- proof
  aesop


-- created on 2026-09-18
