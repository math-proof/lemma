import Mathlib.Analysis.Complex.Trigonometric
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.cosh (-x) = Real.cosh x := by
  -- proof
  exact Real.cosh_neg x

-- created on 2023-11-26
