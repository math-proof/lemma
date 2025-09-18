import Lemma.Basic


/--
This lemma asserts the associativity of the multiplication operation in a semigroup, confirming that the grouping of elements in a product does not affect the result.
Specifically, it states that for any elements `a`, `b`, and `c` in a semigroup, the product `a * b * c` is equal to `a * (b * c)`, leveraging the inherent associative property of the semigroup's binary operation.
-/
@[main, comm]
private lemma main
  [Semigroup α]
  {a b : α} :
-- imply
  a * b * c = a * (b * c) := by
-- proof
  rw [mul_assoc]


-- created on 2024-07-01
-- updated on 2025-04-04
