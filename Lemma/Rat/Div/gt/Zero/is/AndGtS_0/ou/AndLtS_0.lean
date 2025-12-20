import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : α) :
-- imply
  a / b > 0 ↔ a > 0 ∧ b > 0 ∨ a < 0 ∧ b < 0 :=
-- proof
  div_pos_iff


-- created on 2025-12-08
