import sympy.Basic


@[main, comm, mp, mpr]
private lemma main:
-- imply
  q → p ↔ ¬p → ¬q := by
-- proof
  constructor <;>
    intro h
  .
    intro hq hp
    have := h hp
    contradiction
  .
    intro hq
    aesop


-- created on 2024-07-01
