import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {a b : ℝ} :
-- imply
  Real.arctan (if p then a else b) = if p then Real.arctan a else Real.arctan b :=
-- proof
  apply_ite Real.arctan p a b


-- created on 2022-01-20
-- updated on 2026-10-17
