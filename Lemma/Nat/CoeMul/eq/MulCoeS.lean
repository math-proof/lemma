import sympy.Basic


@[main, comm]
private lemma main
  [NonAssocSemiring α]
  {a b : ℕ} :
-- imply
  ((a * b : ℕ) : α) = a * b :=
-- proof
  Nat.cast_mul a b


-- created on 2025-03-30
-- updated on 2025-10-08
