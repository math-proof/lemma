import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
-- given
  (h : f x ∈ Set.Ioi 1) :
-- imply
  0 < Real.log (f x) := by
-- proof
  exact Real.log_pos h


-- created on 2023-04-17
-- updated on 2026-10-26
