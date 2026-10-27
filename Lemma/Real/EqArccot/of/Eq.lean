import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x = y) :
-- imply
  Real.pi / 2 - Real.arctan x = Real.pi / 2 - Real.arctan y :=
-- proof
  congr_arg (fun t : ℝ => Real.pi / 2 - Real.arctan t) h₀


-- created on 2022-01-20
-- updated on 2026-10-26
