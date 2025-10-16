import sympy.Basic


@[main, comm]
private lemma main
  [AddGroupWithOne α]
  {a b : ℤ} :
-- imply
  ((a - b : ℤ) : α) = a - b :=
-- proof
  Int.cast_sub a b


-- created on 2025-03-28
-- updated on 2025-10-16
