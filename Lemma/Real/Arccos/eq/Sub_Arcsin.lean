import Initialize.Tactic.Attr.Basic
import Def.Analysis.SpecialFunctions.Trigonometric.Part2


@[path]
private lemma main
  {x : ℝ} :
-- imply
  arccos x = π / 2 - arcsin x :=
-- proof
  Real.arccos_eq_pi_div_two_sub_arcsin x


-- created on 2018-06-13
