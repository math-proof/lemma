import sympy.Basic


@[main]
private lemma Comm
  [CommMagma α]
-- given
  (a b : α) :
-- imply
  a * b = b * a :=
-- proof
  mul_comm a b


-- created on 2025-06-06
