import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {a b : ℝ} :
-- imply
  Real.cot (if p then a else b) = if p then Real.cot a else Real.cot b :=
-- proof
  apply_ite Real.cot p a b


-- created on 2022-01-20
-- updated on 2026-10-17
