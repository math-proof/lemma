import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main :
-- imply
  (p ↔ q) ↔ (¬p ↔ ¬q) := by
-- proof
  constructor <;>
    intro h
  ·
    rw [h]
  ·
    constructor
    · intro hp
      by_contra hnq
      have hnp := h.mpr hnq
      exact hnp hp
    · intro hq
      by_contra hnp
      have hnq := h.mp hnp
      exact hnq hq



-- created on 2024-07-01
-- updated on 2025-08-13
