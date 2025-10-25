import sympy.Basic


@[main, comm, mp, mpr]
private lemma main :
-- imply
  ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
-- proof
  tauto


-- created on 2024-07-01
-- updated on 2025-10-25
