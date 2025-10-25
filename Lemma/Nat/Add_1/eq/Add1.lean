import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid α] [One α]
  {a : α} :
-- imply
  a + 1 = 1 + a := by
-- proof
  apply AddCommMonoid.add_comm


-- created on 2025-04-06
