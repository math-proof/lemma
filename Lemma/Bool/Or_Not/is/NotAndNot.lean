import Lemma.Bool.NotAnd.is.OrNotS
import Lemma.Bool.IffNotNot
open Bool


@[main]
private lemma main:
-- imply
  p ∨ ¬q ↔ ¬(¬p ∧ q) := by
-- proof
  rw [NotAnd.is.OrNotS]
  rw [IffNotNot]


-- created on 2025-04-12
