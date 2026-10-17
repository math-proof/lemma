import Mathlib.Analysis.Calculus.Deriv.Basic
import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {f g : ℝ → ℝ}
  {x : ℝ} :
-- imply
  deriv (fun t => if p then f t else g t) x = if p then deriv f x else deriv g x := by
-- proof
  split_ifs
  · rfl
  · rfl


-- created on 2026-10-11
-- updated on 2026-10-17
