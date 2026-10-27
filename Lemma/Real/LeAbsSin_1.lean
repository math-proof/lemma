import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  |sin x| ≤ 1 :=
-- proof
  Real.abs_sin_le_one x


-- created on 2025-03-25
