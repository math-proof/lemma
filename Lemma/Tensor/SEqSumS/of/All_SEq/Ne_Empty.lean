import Lemma.Finset.All_EqCast.of.All_SEq.Ne_Empty
import Lemma.Finset.Any_In.is.Ne_Empty
import Lemma.Finset.EqSumS.of.All_Eq
import Lemma.Tensor.Sum.as.Sum_Cast.of.Eq
open Finset Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  [DecidableEq ι]
  {S : Finset ι}
  {X : ι → Tensor α s}
  {Y : ι → Tensor α s'}
-- given
  (h_s : S ≠ ∅)
  (h : ∀ i ∈ S, X i ≃ Y i) :
-- imply
  ∑ i ∈ S, X i ≃ ∑ i ∈ S, Y i := by
-- proof
  let ⟨i, hi⟩ := Any_In.of.Ne_Empty h_s
  have hi := h i hi
  have h := All_EqCast.of.All_SEq.Ne_Empty h_s h
  have h := EqSumS.of.All_Eq h
  rw [← h]
  apply Sum.as.Sum_Cast.of.Eq hi.left


-- created on 2025-11-06
