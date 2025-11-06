import Lemma.Finset.All_EqCast.of.All_SEq.Ne_Empty
import Lemma.Finset.Any_In.is.Ne_Empty
import Lemma.Finset.EqSumS.of.All_Eq
import Lemma.Vector.Sum.as.Sum_Cast.of.Eq
import stdlib.SEq
import sympy.vector.vector
open Finset Vector


@[main]
private lemma main
  [AddCommMonoid α]
  {s : Finset ι}
  {x : ι → List.Vector α n}
  {y : ι → List.Vector α n'}
-- given
  (h_s : s ≠ ∅)
  (h : ∀ i ∈ s, x i ≃ y i) :
-- imply
  ∑ i ∈ s, x i ≃ ∑ i ∈ s, y i := by
-- proof
  let ⟨i, hi⟩ := Any_In.of.Ne_Empty h_s
  have hi := h i hi
  have h := All_EqCast.of.All_SEq.Ne_Empty h_s h
  have h := EqSumS.of.All_Eq h
  rw [← h]
  apply Sum.as.Sum_Cast.of.Eq hi.left


-- created on 2025-11-06
