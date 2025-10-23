import sympy.Basic


@[main, comm]
private lemma main
  [SubNegMonoid α]
-- given
  (a b : α) :
-- imply
  a - b = a + -b :=
-- proof
  sub_eq_add_neg a b


-- created on 2024-07-01
-- updated on 2025-04-04
