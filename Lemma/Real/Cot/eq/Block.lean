import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (v : Fin n → ℝ) :
-- imply
  Real.cot ∘ v = fun i => Real.cot (v i) :=
-- proof
  rfl


-- created on 2023-06-08
-- updated on 2026-10-26
