import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  Real.sec x = Real.sec y :=
-- proof
  congr_arg Real.sec h


-- created on 2022-01-23
-- updated on 2026-10-26
