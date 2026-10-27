import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.csc x = (Real.sin x)⁻¹ := by
  -- proof
  simp [Real.csc]


-- created on 2023-10-03
