import Lemma.Finset.Sum.of.All_Eq
open Finset


@[main]
private lemma main
  [AddCommMonoid β]
  {x y : Fin n → β}
-- given
  (h : ∀ i : Fin n, x i = y i) :
-- imply
  ∑ i : Fin n, x i = ∑ i : Fin n, y i := by
-- proof
  apply Sum.of.All_Eq
  aesop


-- created on 2025-12-01
