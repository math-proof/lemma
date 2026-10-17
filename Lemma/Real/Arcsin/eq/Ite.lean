import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {a b : ℝ} :
-- imply
  Real.arcsin (if p then a else b) = if p then Real.arcsin a else Real.arcsin b :=
-- proof
  apply_ite Real.arcsin p a b


-- created on 2026-10-11
-- updated on 2026-10-17
