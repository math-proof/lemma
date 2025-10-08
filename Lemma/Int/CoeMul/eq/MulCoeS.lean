import sympy.Basic


@[main, comm]
private lemma main
  [NonAssocRing α]
  {a b : ℤ} :
-- imply
  ((a * b : ℤ) : α) = a * b :=
-- proof
  Int.cast_mul a b


-- created on 2025-10-08
