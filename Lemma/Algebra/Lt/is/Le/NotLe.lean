import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
  {a b : α} :
-- imply
  a < b ↔ a ≤ b ∧ ¬(b ≤ a) :=
-- proof
  lt_iff_le_not_ge


-- created on 2025-08-02
