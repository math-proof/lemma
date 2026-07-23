import Lemma.Finset.Sum_Add.eq.AddSumS
open Finset


@[main, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (a b : Fin n → α) :
-- imply
  ∑ i : Fin n, (a i + b i) = ∑ i : Fin n, a i + ∑ i : Fin n, b i := by
-- proof
  apply Sum_Add.eq.AddSumS


-- created on 2026-07-23
