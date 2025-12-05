import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [Ring α]
  {x : α} :
-- imply
  (-x)² = x² := by
-- proof
  rw [sq, sq]
  simp [mul_neg, neg_mul, neg_neg]


-- created on 2025-04-06
