import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  (x + y).sin = x.sin * y.cos + y.sin * x.cos := by
-- proof
  grind [Real.sin_add]


-- created on 2020-11-24
-- updated on 2026-10-26
