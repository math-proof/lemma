import Lemma.Finset.LeSumS.of.All_Le
open Finset


@[main]
private lemma main
  [AddCommMonoid N] [PartialOrder N] [IsOrderedAddMonoid N]
  {s : Finset ι}
  {x y : ι → N}
-- given
  (h : ∀ i ∈ s, x i ≥ y i) :
-- imply
  ∑ i ∈ s, x i ≥ ∑ i ∈ s, y i :=
-- proof
  LeSumS.of.All_Le (x := y) (y := x) h


-- created on 2025-04-06
