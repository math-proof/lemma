import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  (v : Fin n → ℝ) :
-- imply
  Real.cot ∘ v = fun i => Real.cot (v i) :=
-- proof
  rfl


-- created on 2026-10-11
-- updated on 2026-10-17
