import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  Real.csc x = Real.csc y :=
-- proof
  congr_arg Real.csc h


-- created on 2022-01-23
-- updated on 2026-10-26
