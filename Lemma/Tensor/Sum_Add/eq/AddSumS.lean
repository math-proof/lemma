import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Tensor.EqSumStack
import Lemma.Tensor.Sum.eq.Zero
import Lemma.Tensor.SumStack.eq.AddSumSStack
open Nat Tensor


@[main, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (A B : Fin n → Tensor α s) :
-- imply
  ∑ i < n, (A i + B i) = ∑ i < n, A i + ∑ i < n, B i := by
-- proof
  induction n generalizing s with
  | zero =>
    rw [Sum.eq.Zero]
    conv_rhs => rw [Sum.eq.Zero]
    conv_rhs =>
      arg 2
      rw [Sum.eq.Zero]
    grind
  | succ n ih =>
    have := SumStack.eq.AddSumSStack.fin (fun i : Fin (n + 1) => A i + B i)
    apply this.trans
    erw [ih]
    have := SumStack.eq.AddSumSStack.fin (fun i : Fin (n + 1) => A i)
    simp at this
    rw [this]
    have := SumStack.eq.AddSumSStack.fin (fun i : Fin (n + 1) => B i)
    simp at this
    rw [this]
    erw [Add_Add.eq.AddAdd]
    conv_rhs =>
      arg 1
      erw [AddAdd.comm]
    rw [AddAdd.eq.Add_Add]
    congr 1
    repeat rw [EqSumStack.fn]
    rfl


-- created on 2026-07-23
