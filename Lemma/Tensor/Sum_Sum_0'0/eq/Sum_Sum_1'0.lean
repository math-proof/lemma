import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.Eq
import Lemma.Fin.Sum.of.All_Eq
import Lemma.Finset.Sum_Sum
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt.GtGet_0.GtLength_0
import Lemma.Tensor.GetSum.eq.Sum_Get.of.GtLength_0
import Lemma.Tensor.Sum.eq.Sum_Select
import Lemma.Tensor.Sum_0.eq.SumStack_Get
import Lemma.Tensor.Sum_0.eq.Sum_Get
open Bool Fin Finset Tensor


@[main, fin, cast, cast.fin]
private lemma main
  [AddCommMonoid α]
-- given
  (h : s.length > 1)
  (X : Tensor α s) :
-- imply
  (X.sum 0).sum 0 ≃ (X.sum 1).sum 0 := by
-- proof
  match s with
  | [] =>
    contradiction
  | [m] =>
    contradiction
  | m :: n :: s =>
    rw [Sum_0.eq.Sum_Get]
    erw [Sum_0.eq.Sum_Get]
    erw [Sum_0.eq.Sum_Get]
    erw [Sum.eq.Sum_Select X ⟨1, by grind⟩]
    simp only [GetElem.getElem]
    have h_all : ∀ j : Fin m, (∑ k : Fin (m :: n :: s)[1], X.select ⟨1, by grind⟩ k : Tensor α ((m :: n :: s).eraseIdx 1)).get ⟨j, by grind⟩ = ∑ k, (X.select ⟨1, by grind⟩ k).get ⟨j, by grind⟩ := by
      intro j
      apply GetSum.eq.Sum_Get.of.GtLength_0.fin (by grind)
    have h_sum := Sum.of.All_Eq h_all
    have h_sum := SEq.of.Eq h_sum
    symm
    apply h_sum.trans
    have h_all : ∀ j : Fin n, (∑ i : Fin m, X.get ⟨i, by grind⟩ : Tensor α (m :: n :: s).tail).get ⟨j, by grind⟩ = ∑ i : Fin m, (X.get ⟨i, by grind⟩).get ⟨j, by grind⟩ := by
      intro j
      apply GetSum.eq.Sum_Get.of.GtLength_0.fin (by grind)
    have h_sum := Sum.of.All_Eq h_all
    have h_sum := SEq.of.Eq h_sum
    symm
    apply h_sum.trans
    rw [Sum_Sum.comm]
    apply SEq.of.Eq
    apply @Fin.Sum.of.All_Eq
    intro i
    apply @Fin.Sum.of.All_Eq
    intro j
    erw [GetSelect_1.eq.Cast_Get.of.Lt.GtGet_0.GtLength_0 (by grind) (by grind) (by grind)]
    apply Eq_Cast.of.SEq
    rfl


@[main, fin, cast.fin]
private lemma stack
  [AddCommMonoid α]
-- given
  (h : s.length > 1)
  (X : Tensor α s) :
-- imply
  (X.sum 0).sum 0 ≃ (X.sum 1).sum 0 := by
-- proof
  match s with
  | [] =>
    contradiction
  | [m] =>
    contradiction
  | m :: n :: s =>
    rw [Sum_0.eq.SumStack_Get]
    erw [Sum_0.eq.SumStack_Get]
    erw [Sum_0.eq.SumStack_Get]
    erw [Sum.eq.Sum_Select X ⟨1, by grind⟩]
    simp only [GetElem.getElem]
    have h_all : ∀ j : Fin m, (∑ k : Fin (m :: n :: s)[1], X.select ⟨1, by grind⟩ k : Tensor α ((m :: n :: s).eraseIdx 1)).get ⟨j, by grind⟩ = ∑ k, (X.select ⟨1, by grind⟩ k).get ⟨j, by grind⟩ := by
      intro j
      apply GetSum.eq.Sum_Get.of.GtLength_0.fin (by grind)
    have h_sum := Sum.of.All_Eq h_all
    have h_sum := SEq.of.Eq h_sum
    symm
    apply h_sum.trans
    have h_all : ∀ j : Fin n, (∑ i : Fin m, X.get ⟨i, by grind⟩ : Tensor α (m :: n :: s).tail).get ⟨j, by grind⟩ = ∑ i : Fin m, (X.get ⟨i, by grind⟩).get ⟨j, by grind⟩ := by
      intro j
      apply GetSum.eq.Sum_Get.of.GtLength_0.fin (by grind)
    have h_sum := Sum.of.All_Eq h_all
    have h_sum := SEq.of.Eq h_sum
    symm
    apply h_sum.trans
    rw [Sum_Sum.comm]
    apply SEq.of.Eq
    apply @Fin.Sum.of.All_Eq
    intro i
    apply @Fin.Sum.of.All_Eq
    intro j
    erw [GetSelect_1.eq.Cast_Get.of.Lt.GtGet_0.GtLength_0 (by grind) (by grind) (by grind)]
    apply Eq_Cast.of.SEq
    rfl


-- created on 2026-07-22
