import Lemma.Tensor.Stack.eq.AppendStackS
import Lemma.Tensor.Sum.eq.Zero
import Lemma.Tensor.SumAppend.eq.AddSumS
open Tensor


@[main]
private lemma main
  [AddMonoid α]
-- given
  (X : ℕ → Tensor α s)
  (n k : ℕ) :
-- imply
  let lhs : Tensor α s := ∑ i < n, X i
  let rhs : Tensor α s := ∑ i < k, X (n + i)
  ∑ i < n + k, X i = lhs + rhs := by
-- proof
  simp
  rw [Stack.eq.AppendStackS (f := fun i => X i)]
  rw [SumAppend.eq.AddSumS]


@[main]
private lemma fin
  [AddMonoid α]
-- given
  (X : Fin (n + k) → Tensor α s) :
-- imply
  let lhs : Tensor α s := ∑ i < n, X ⟨i, by grind⟩
  let rhs : Tensor α s := ∑ i < k, X ⟨n + i, by grind⟩
  ∑ i < n + k, X ⟨i, by grind⟩ = lhs + rhs := by
-- proof
  if h : n + k = 0 then
    have h_n : n = 0 := by grind
    have h_j : k = 0 := by grind
    subst h_n
    subst h_j
    simp
    rw [Sum.eq.Zero]
    grind
  else
    have := main (fun i => if h_i : i < n + k then
      X ⟨i, by grind⟩
    else
      X ⟨0, by grind⟩) n k
    grind


-- created on 2026-07-22
-- updated on 2026-07-23
