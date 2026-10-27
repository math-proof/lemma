import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : Real.cot x = Real.cot y) :
-- imply
  Real.cot x = Real.cot y :=
-- proof
  h


-- created on 2022-01-23
-- updated on 2026-10-26
