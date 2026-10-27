import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.sin x ≠ 0) :
-- imply
  Real.csc x * Real.sin x = 1 := by
-- proof
  simp [Real.csc, h]


-- created on 2023-10-03
