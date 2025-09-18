import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main :
-- imply
  ¬(p → q) ↔ p ∧ ¬q := by
-- proof
  constructor <;>
  · 
    intro h
    simp_all


-- created on 2024-07-01
-- updated on 2025-07-30
