import Theorem.Algebra.BigOperators.Reduced.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Fintype α]
-- given
  (v : α → ℝ) :
-- imply
  v.sum = ∑ b, v b := by
-- proof
  exact rfl


-- created on 2026-10-07
