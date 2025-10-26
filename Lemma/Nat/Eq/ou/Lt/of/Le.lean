import sympy.Basic


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  a = b ∨ a < b :=
-- proof
  eq_or_lt_of_le h


-- created on 2025-03-23
