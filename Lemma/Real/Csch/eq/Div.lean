import Mathlib.Analysis.Complex.Trigonometric
import Def.Analysis.SpecialFunctions.Hyperbolic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.csch x = 2 / (Real.exp x - Real.exp (-x)) := by
-- proof
  rw [Real.csch, Real.sinh_eq]
  field_simp


-- created on 2023-11-26
-- updated on 2026-10-26
