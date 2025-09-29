import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  {a b : α} :
-- imply
  a ≠ b ↔ ¬a = b := by
-- proof
  constructor <;>
  ·
    intro h h_eq
    contradiction


-- created on 2025-04-20
