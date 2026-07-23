import Lemma.Finset.Sum_Sum
open Finset


@[main]
private lemma Comm
  [AddCommMonoid α]
-- given
  (f : Fin m → Fin n → α) :
-- imply
  ∑ i : Fin m, ∑ j : Fin n, f i j = ∑ j : Fin n, ∑ i : Fin m, f i j :=
-- proof
  Sum_Sum.comm Finset.univ Finset.univ f


-- created on 2026-07-23
