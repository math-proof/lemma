import Lemma.Set.NotIn.of.Ne.Ne
import Lemma.Logic.NotOr.is.AndNotS
open Set Logic


@[main]
private lemma main
  {a b e : α}
-- given
  (h : e ∈ ({a, b} : Set α)) :
-- imply
  e = a ∨ e = b := by
-- proof
  by_contra h
  have := AndNotS.of.NotOr h
  have := NotIn.of.Ne.Ne this.left this.right
  contradiction


-- created on 2025-04-20
