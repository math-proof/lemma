import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.Tensor.GetSum.eq.Sum_Get.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Ne_Nil
import sympy.tensor.tensor
open Tensor List


@[main]
private lemma main
  [AddCommMonoid α]
  [DecidableEq ι]
-- given
  (h : s = s')
  (S : Finset ι)
  (X : ι → Tensor α s) :
-- imply
  ∑ i ∈ S, X i ≃ ∑ i ∈ S, cast (congrArg (Tensor α) h) (X i) := by
-- proof
  if h_s : s = [] then
    subst h_s
    aesop
  else
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil h_s h
    intro i
    have h_s := GtLength_0.of.Ne_Nil h_s
    have h_i : i < s[0] := by simp [← Length.eq.Get_0.of.GtLength_0 h_s (∑ i ∈ S, X i)]
    rw [GetSum.eq.Sum_Get.of.GtLength_0 h_s X ⟨i, h_i⟩]
    let X' : ι → Tensor α s' := fun j => cast (congrArg (Tensor α) h) (X j)
    have := GetSum.eq.Sum_Get.of.GtLength_0 (h ▸ h_s) X' ⟨i, h ▸ h_i⟩
    aesop


-- created on 2025-11-06
