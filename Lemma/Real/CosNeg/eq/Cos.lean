import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Cos.cos (-x) = Cos.cos x :=
-- proof
  Real.cos_neg x


-- created on 2026-09-03
