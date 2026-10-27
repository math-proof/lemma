import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : Real.sin x = Real.sin y) :
-- imply
  Real.sin x = Real.sin y :=
-- proof
  h


-- created on 2022-01-23
-- updated on 2026-10-26
