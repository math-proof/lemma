import Initialize.Tactic.Attr.Basic
import Def.Analysis.SpecialFunctions.Trigonometric.Part2


@[path]
private lemma main
  {x : ℝ}
  {A : Set ℝ}
  [DecidablePred (· ∈ A)]
  {f g : ℝ → ℝ} :
-- imply
  Real.arccos (if x ∈ A then f x else g x) = if x ∈ A then Real.arccos (f x) else Real.arccos (g x) := by
-- proof
  exact apply_ite Real.arccos _ _ _


-- created on 2022-01-20
-- updated on 2026-10-26
