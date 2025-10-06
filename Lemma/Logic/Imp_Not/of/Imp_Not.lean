import Lemma.Logic.Imp.is.ImpNotS
import Lemma.Logic.IffNotNot
open Logic


@[main]
private lemma main
-- given
  (h : p → ¬q) :
-- imply
  q → ¬p := by
-- proof
  have := ImpNotS.of.Imp h
  rwa [IffNotNot] at this


-- created on 2025-04-14
