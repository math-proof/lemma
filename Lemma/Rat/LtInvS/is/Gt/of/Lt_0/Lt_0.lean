import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Field α]
  [LinearOrder α]
  [IsStrictOrderedRing α]
  {a b : α}
-- given
  (ha : a < 0)
  (hb : b < 0) :
-- imply
  a⁻¹ < b⁻¹ ↔ a > b :=
-- proof
  inv_lt_inv_of_neg ha hb


-- created on 2025-12-08
