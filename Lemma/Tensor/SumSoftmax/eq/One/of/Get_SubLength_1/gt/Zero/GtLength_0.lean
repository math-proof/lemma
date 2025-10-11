import sympy.tensor.functions
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Softmax.eq.MkSoftmaxData
import Lemma.Tensor.Sum.eq.MkListSumData
import Lemma.Vector.SumSoftmax.eq.One
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Nat.Eq_0
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
      have h_1 : (1 : Tensor α ([s₀].eraseIdx ([s₀].length - 1))).data = 1 := rfl
      rw [h_1]
      simp [Vector.EqGet1'1.fin]
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
      sorry


-- created on 2025-10-07
-- updated on 2025-10-11
