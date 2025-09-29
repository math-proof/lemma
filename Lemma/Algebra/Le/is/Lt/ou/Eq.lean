import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [PartialOrder α]
  {a b : α} :
-- imply
  a ≤ b ↔ a < b ∨ a = b :=
-- proof
  le_iff_lt_or_eq


-- created on 2025-03-29
