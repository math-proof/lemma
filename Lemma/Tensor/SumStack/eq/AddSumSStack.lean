import Lemma.Tensor.Stack.eq.AppendStackS
import Lemma.Tensor.SumAppend.eq.AddSumS
open Tensor


@[main]
private lemma main
  [AddMonoid α]
-- given
  (X : ℕ → Tensor α s)
  (n : ℕ) :
-- imply
  let lhs : Tensor α s := ∑ i < n, X i
  let rhs : Tensor α s := ∑ i < j, X (n + i)
  ∑ i < n + j, X i = lhs + rhs := by
-- proof
  simp
  rw [Stack.eq.AppendStackS (f := fun i => X i)]
  rw [SumAppend.eq.AddSumS]


-- created on 2026-07-22
