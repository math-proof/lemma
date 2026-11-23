import Theorem.Algebra.Power.Part2
import Notation.Algebra.Power
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Ring α]
  {x : α} :
-- imply
  (-x)² = x² := by
-- proof
  rw [sq, sq]
  simp [mul_neg, neg_mul, neg_neg]


-- created on 2025-04-06
-- updated on 2026-11-23
