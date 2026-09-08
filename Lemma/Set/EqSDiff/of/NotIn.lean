import Lemma.Set.EqSDiff.of.Inter.eq.Empty
import Lemma.Set.Inter_Finset.eq.Empty.of.NotIn
open Set


@[main]
private lemma main
  {e : α}
  {S : Set α}
-- given
  (h : e ∉ S) :
-- imply
  S \ {e} = S := by
-- proof
  apply EqSDiff.of.Inter.eq.Empty
  apply Inter_Finset.eq.Empty.of.NotIn h


-- created on 2019-02-01
-- updated on 2026-09-08
