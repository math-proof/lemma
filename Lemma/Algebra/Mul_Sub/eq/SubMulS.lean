import sympy.Basic


@[main, comm]
private lemma nat
-- given
  (x a b : ℕ) :
-- imply
  x * (a - b) = x * a - x * b :=
-- proof
  Nat.mul_sub x a b


@[main, comm]
private lemma main
  [NonUnitalNonAssocRing α]
-- given
  (x a b : α) :
-- imply
  x * (a - b) = x * a - x * b :=
-- proof
  mul_sub x a b


-- created on 2024-07-01
-- updated on 2025-03-31
