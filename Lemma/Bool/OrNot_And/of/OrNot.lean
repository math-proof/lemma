import Lemma.Logic.Or_AndNot.of.Or
import Lemma.Bool.IffNotNot
open Logic Bool


@[main]
private lemma main
-- given
  (h : ¬p ∨ q) :
-- imply
  ¬p ∨ (p ∧ q) := by
-- proof
  have := Or_AndNot.of.Or h
  rwa [IffNotNot] at this


-- created on 2025-04-07
