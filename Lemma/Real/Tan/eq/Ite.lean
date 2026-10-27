import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {a b : ℝ} :
-- imply
  Real.tan (if p then a else b) = if p then Real.tan a else Real.tan b :=
-- proof
  apply_ite Real.tan p a b


-- created on 2022-01-20
-- updated on 2026-10-26
