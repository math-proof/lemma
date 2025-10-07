import Lemma.Logic.NotAnd.is.OrNotS
import Lemma.Bool.IffNotNot
open Logic Bool


@[main]
private lemma main:
-- imply
  p ∨ ¬q ↔ ¬(¬p ∧ q) := by
-- proof
  rw [NotAnd.is.OrNotS]
  rw [IffNotNot]


-- created on 2025-04-12
