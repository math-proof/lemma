import Lemma.Finset.LtSumS.of.Any_Lt.All_Le
open Finset


@[main]
private lemma main
  [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N]
  {s : Finset ι}
  {x y : ι → N}
-- given
  (h₀ : ∀ i ∈ s, x i ≥ y i)
  (h₁ : ∃ i ∈ s, x i > y i) :
-- imply
  ∑ i ∈ s, x i > ∑ i ∈ s, y i :=
-- proof
  LtSumS.of.Any_Lt.All_Le (x := y) (y := x) h₀ h₁


-- created on 2025-10-08
