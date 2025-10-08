import sympy.Basic


@[main, comm]
private lemma main
  [AddGroupWithOne α]
-- given
  (a b : ℤ) :
-- imply
  ((a + b : ℤ) : α) = a + b :=
-- proof
  Int.cast_add a b


-- created on 2025-10-08
