import Mathlib.Analysis.Calculus.Deriv.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (c x : ℝ) :
-- imply
  deriv (fun _ : ℝ => c) x = 0 := by
-- proof
  rw [deriv_const]


-- created on 2023-06-21
-- updated on 2026-10-26
