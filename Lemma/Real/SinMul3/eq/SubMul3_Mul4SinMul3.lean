import Theorem.Algebra.Power.Part2
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  sin (3 * x) = 3 * sin x - 4 * (sin x)³ :=
-- proof
  Real.sin_three_mul x


-- created on 2025-03-24
-- updated on 2026-10-26
