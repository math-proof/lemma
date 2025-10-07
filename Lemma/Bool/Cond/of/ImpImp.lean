import Lemma.Bool.NotImp.is.And_Not
import Lemma.Bool.Imp.is.ImpNotS
import Lemma.Bool.False.of.AndNot
open Bool


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
