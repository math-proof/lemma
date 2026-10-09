import Lemma.Set.Neg.in.Icc.of.In_Icc
open Set


@[path]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x a b : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  -x ∈ Icc (-b) (-a) := by
-- proof
  exact Neg.in.Icc.of.In_Icc h


-- created on 2026-10-03
