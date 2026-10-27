import Def.Analysis.SpecialFunctions.Hyperbolic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.cosh x = 1 / Real.sech x := by
-- proof
  simp [Real.sech]


-- created on 2023-11-26
