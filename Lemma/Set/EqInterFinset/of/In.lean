import Lemma.Set.SubsetFinset.of.In
import Lemma.Set.EqInter.of.Subset
open Set


@[path]
private lemma main
  {a : α}
  {s : Set α}
-- given
  (h : a ∈ s) :
-- imply
  {a} ∩ s = {a} := by
-- proof
  have := SubsetFinset.of.In h
  apply EqInter.of.Subset.left this


-- created on 2025-05-18
