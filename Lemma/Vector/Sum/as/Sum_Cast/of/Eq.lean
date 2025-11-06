import Lemma.Nat.LtVal
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetSum.eq.Sum_Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Vector


@[main]
private lemma main
  [AddCommMonoid α]
  [DecidableEq ι]
-- given
  (h : n = n')
  (s : Finset ι)
  (x : ι → List.Vector α n) :
-- imply
  ∑ i ∈ s, x i ≃ ∑ i ∈ s, cast (congrArg (List.Vector α) h) (x i) := by
-- proof
  apply SEq.of.All_EqGetS.Eq h
  intro i
  rw [GetSum.eq.Sum_Get]
  have h_i := LtVal i
  simp [h] at h_i
  let x' : ι → List.Vector α n' := fun j => cast (congrArg (List.Vector α) h) (x j)
  have := GetSum.eq.Sum_Get s x' ⟨i, h_i⟩
  aesop


-- created on 2025-11-06
