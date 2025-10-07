import Lemma.Bool.Imp.is.OrNot
open Bool


@[main, comm, mp, mpr]
private lemma main :
-- imply
  p ∨ q ↔ ¬p → q := by
-- proof
  rw [Imp.is.OrNot]
  simp


-- created on 2025-01-12
