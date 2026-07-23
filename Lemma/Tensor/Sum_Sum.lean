import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.EqStack_0'0
import Lemma.Tensor.EqSum0_0
import Lemma.Tensor.EqSumStack
import Lemma.Tensor.SEqAddS.of.SEq.SEq
import Lemma.Tensor.Sum.eq.Zero
import Lemma.Tensor.SumStack.eq.AddSumSStack
import Lemma.Tensor.SumStack.of.All_Eq
import Lemma.Tensor.Sum_Add.eq.AddSumS
open Bool Tensor
set_option maxHeartbeats 1000000


@[main]
private lemma Comm
  [AddCommMonoid α]
-- given
  (f : Fin m → Fin n → Tensor α s) :
-- imply
  ∑ i < m, ∑ j < n, f i j = ∑ j < n, ∑ i < m, f i j := by
-- proof
  induction m generalizing n s with
  | zero =>
    rw [Sum.eq.Zero]
    have h_all : ∀ j : Fin n, (∑ i < 0, f i j : Tensor α s) = 0 := by
      intro j
      rw [Sum.eq.Zero]
    rw [SumStack.of.All_Eq h_all, EqStack_0'0, EqSum0_0]
    rfl
  | succ m ih =>
    erw [SumStack.eq.AddSumSStack.fin (fun i : Fin (m + 1) => ∑ j < n, f i j)]
    rw [ih]
    have h_all : ∀ j : Fin n, (∑ i < m + 1, f i j : Tensor α s) =
      let lhs : Tensor α s := ∑ i < m, f ⟨i, by grind⟩ j
      let rhs : Tensor α s := ∑ i < 1, f ⟨m, by grind⟩ j
      lhs + rhs := by
      intro j
      simp [SumStack.eq.AddSumSStack.fin (fun i : Fin (m + 1) => f i j)]
    simp at h_all
    have h_sum := SumStack.of.All_Eq h_all
    symm
    apply h_sum.trans
    conv_lhs => erw [Sum_Add.eq.AddSumS]
    apply Eq.of.SEq
    apply SEqAddS.of.SEq.SEq
    ·
      rfl
    ·
      erw [EqSumStack.fn]
      simp
      have h_all : ∀ i : Fin n, ∑ j < 1, f ⟨m, by grind⟩ i = f ⟨m, by grind⟩ i := by
        intro i
        erw [EqSumStack]
      simp at h_all
      have h_sum := SumStack.of.All_Eq h_all
      apply SEq.of.Eq
      apply h_sum.trans
      rfl


-- created on 2026-07-23
