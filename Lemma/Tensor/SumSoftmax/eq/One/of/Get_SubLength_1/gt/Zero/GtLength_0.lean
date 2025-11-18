import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Softmax.eq.MkSoftmaxData
import Lemma.Tensor.Sum.eq.MkListSumData
import Lemma.Vector.SumSoftmax.eq.One
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Nat.Eq_0
import Lemma.Vector.EqGet1'1
import Lemma.Tensor.EqGet1'1
import Lemma.Tensor.GetSum.eq.Cast_SumGet.of.Lt_Get_0.Gt_0.Lt_Length
import Lemma.Tensor.EqData1'1
import Lemma.Tensor.GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.Gt_0.Lt_Length
open Tensor Vector Nat


@[main]
private lemma main
  [ExpPos α] [IsOrderedCancelAddMonoid α]
-- given
  (h_s : s.length > 0)
  (h : s[s.length - 1] > 0)
  (X : Tensor α s) :
-- imply
  (X.softmax).sum = 1 := by
-- proof
  induction s with
  | nil =>
    contradiction
  | cons s₀ s ih =>
    match s with
    | .nil =>
      rw [Softmax.eq.MkSoftmaxData]
      rw [Sum.eq.MkListSumData]
      simp
      apply Eq.of.EqDataS
      simp
      ext i
      rw [EqData1'1]
      simp [EqGet1'1.fin (n := [].prod)]
      have h_0 := Eq_0 i
      subst h_0
      simp [List.Vector.get]
      simp at h
      have : NeZero (s₀ * 1) := by
        simp
        constructor
        omega
      rw [SumSoftmax.eq.One]
    | .cons s₁ s =>
      apply Eq.of.All_EqGetS (m := s₀)
      intro i
      have := GetSum.eq.Cast_SumGet.of.Lt_Get_0.Gt_0.Lt_Length (by simp) (by simp) (by simp) X.softmax (dim := (s₀ :: s₁ :: s).length - 1) (i := i)
      simp at this
      simp [this]
      have := EqGet1'1 (s := (s₀ :: s₁ :: s).eraseIdx ((s₀ :: s₁ :: s).length - 1)) (i := i) (α := α)
      simp at this
      simp [this]
      rw [GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.Gt_0.Lt_Length (by simp) (by simp) (by simp)]
      exact ih (by simp) (by simp_all) X[i]


-- created on 2025-10-07
-- updated on 2025-10-12
