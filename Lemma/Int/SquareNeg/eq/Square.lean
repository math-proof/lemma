import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [Ring α]
  {x : α} :
-- imply
  (-x)² = x² := by
-- proof
    -- Use the property of additive inverses in rings: (-a) * (-b) = a * b
  rw [sq, sq]
    -- Apply the ring property to show that (-x) * (-x) = x * x
  simp [mul_neg, neg_mul, neg_neg]


-- created on 2025-04-06
