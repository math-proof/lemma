import Lemma.Set.SubsetSingleton.of.In
import Lemma.Set.EqInter.of.Subset
open Set


@[main]
private lemma main
  {a : α}
  {s : Set α}
-- given
  (h : a ∈ s) :
-- imply
  {a} ∩ s = {a} := by
-- proof
  have := SubsetSingleton.of.In h
  apply EqInter.of.Subset.left this


-- created on 2025-05-18
