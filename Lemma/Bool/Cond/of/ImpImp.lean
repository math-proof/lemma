import Lemma.Logic.NotImp.is.And_Not
import Lemma.Logic.Imp.is.ImpNotS
import Lemma.Logic.False.of.AndNot
open Logic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : (p → q) → p) :
-- imply
  p := by
-- proof
  by_contra hq
  have h' := ImpNotS.of.Imp h
  have h' := And_Not.of.NotImp (h' hq)
  apply False.of.AndNot (And.intro hq h'.left)


-- created on 2024-07-01
