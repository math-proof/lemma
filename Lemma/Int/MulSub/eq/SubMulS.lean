import sympy.Basic


@[main, comm]
private lemma main
  [NonUnitalNonAssocRing α]
-- given
  (x a b : α) :
-- imply
  (a - b) * x = a * x - b * x :=
-- proof
  sub_mul a b x


-- created on 2024-11-26
-- updated on 2025-10-16
