import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {a b : ℝ} :
-- imply
  (Real.pi / 2 - Real.arctan (if p then a else b)) =
    if p then Real.pi / 2 - Real.arctan a else Real.pi / 2 - Real.arctan b := by
-- proof
  split_ifs
  · rfl
  · rfl


-- created on 2026-10-11
-- updated on 2026-10-17
