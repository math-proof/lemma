import Lemma.Tensor.SumAppend.eq.AddSumS
import Lemma.Tensor.EqSumStack
import Lemma.Tensor.Stack.eq.AppendStackS
import Lemma.Tensor.Sum.eq.Zero
open Tensor


@[main]
private lemma main
  [AddMonoid α]
  {f : Tensor α s → Tensor α s'}
-- given
  (h₀ : f 0 = 0)
  (h_add : ∀ A B, f (A + B) = f A + f B)
  (X : ℕ → Tensor α s) :
-- imply
  f (∑ i < n, X i) = ∑ i < n, f (X i) := by
-- proof
  induction n with
  | zero =>
    repeat rw [Sum.eq.Zero]
    aesop
  | succ n ih =>
    erw [Stack.eq.AppendStackS (f := fun i => X i)]
    erw [Stack.eq.AppendStackS (f := fun i => f (X i))]
    simp
    erw [SumAppend.eq.AddSumS]
    rw [SumAppend.eq.AddSumS]
    rw [h_add]
    congr 1
    simp [EqSumStack]


@[main]
private lemma fin
  [AddMonoid α]
  {f : Tensor α s → Tensor α s'}
-- given
  (h₀ : f 0 = 0)
  (h_add : ∀ A B, f (A + B) = f A + f B)
  (X : Fin n → Tensor α s) :
-- imply
  f (∑ i < n, X i) = ∑ i < n, f (X i) := by
-- proof
  if h_n : n = 0 then
    subst h_n
    repeat rw [Sum.eq.Zero]
    aesop
  else
    have := main h₀ h_add (fun i => if h_i : i < n then
      X ⟨i, by grind⟩
    else
      X ⟨0, by grind⟩) (α := α) (n := n)
    simp at this
    assumption


-- created on 2026-07-22
