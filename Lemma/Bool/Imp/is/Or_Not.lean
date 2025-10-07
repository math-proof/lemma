import Lemma.Bool.Imp.is.OrNot
open Bool


@[main, comm, mp, mpr]
private lemma main:
-- imply
  (p → q ↔ q ∨ ¬p) := by
-- proof
  rw [Or.comm]
  rw [Imp.is.OrNot]


-- created on 2025-04-05
