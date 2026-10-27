import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.sec x = (Real.cos x)⁻¹ := by
  -- proof
  simp [Real.sec]


-- created on 2023-10-03
