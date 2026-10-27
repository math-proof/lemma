import Def.Analysis.SpecialFunctions.Hyperbolic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sinh x = 1 / Real.csch x := by
-- proof
  simp [Real.csch]


-- created on 2023-11-26
