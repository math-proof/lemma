import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sin x = 1 / Real.csc x := by
-- proof
  simp [Real.csc]


-- created on 2023-11-26
