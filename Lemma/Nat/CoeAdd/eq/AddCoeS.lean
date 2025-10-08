import sympy.Basic


@[main, comm]
private lemma main
  [AddMonoidWithOne α]
-- given
  (a b : ℕ) :
-- imply
  ((a + b : ℕ) : α) = a + b :=
-- proof
  Nat.cast_add a b


-- created on 2025-10-08
