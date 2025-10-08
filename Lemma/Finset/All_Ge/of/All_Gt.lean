import Lemma.Nat.Ge.of.Gt
open Nat


@[main]
private lemma main
  [Preorder N]
  {s : Finset ι}
  {x y : ι → N}
-- given
  (h : ∀ i ∈ s, x i > y i) :
-- imply
  ∀ i ∈ s, x i ≥ y i := by
-- proof
  intro i hi
  specialize h i hi
  apply Ge.of.Gt h


-- created on 2025-10-08
