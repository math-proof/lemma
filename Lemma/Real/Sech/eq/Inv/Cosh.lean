import Mathlib.Analysis.Complex.Trigonometric
import Def.Analysis.SpecialFunctions.Hyperbolic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.sech x = 1 / Real.cosh x := by
  -- proof
  rfl


-- created on 2023-11-26
