import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : Real.pi / 2 - Real.arctan x = Real.pi / 2 - Real.arctan y) :
-- imply
  Real.pi / 2 - Real.arctan x = Real.pi / 2 - Real.arctan y :=
-- proof
  h₀


-- created on 2022-01-23
-- updated on 2026-10-17
