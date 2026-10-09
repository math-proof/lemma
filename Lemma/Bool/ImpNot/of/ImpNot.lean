import Lemma.Bool.Imp.is.ImpNotS
import Lemma.Bool.IffNotNot
open Bool


@[path]
private lemma main
-- given
  (h : ¬p → q) :
-- imply
  ¬q → p := by
-- proof
  have := ImpNotS.of.Imp h
  rwa [IffNotNot] at this


-- created on 2025-04-14
