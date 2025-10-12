import sympy.Basic


@[main, comm]
private lemma main
  [SubtractionCommMonoid α]
-- given
  (a b c : α) :
-- imply
  a - (b + c) = a - b - c :=
-- proof
  sub_add_eq_sub_sub a b c


-- created on 2024-07-01
-- updated on 2025-10-12
