import Lemma.Finset.Sum.of.All_Eq
open Finset


@[main]
private lemma main
  [AddCommMonoid β]
  {x : Fin n → β}
  {y : Fin n' → β}
-- given
  (h_n : n = n')
  (h : ∀ i : Fin n, x i = y (cast (congrArg Fin h_n) i)) :
-- imply
  ∑ i : Fin n, x i = ∑ i : Fin n', y i := by
-- proof
  subst h_n
  apply Sum.of.All_Eq
  simp_all


-- created on 2025-11-28
