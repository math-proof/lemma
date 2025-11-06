import Lemma.Nat.LtVal
import Lemma.Nat.LtVal.of.Eq
import stdlib.SEq
import sympy.tensor.tensor
open Nat


@[main]
private lemma main
  [AddCommMonoid α]
  {X : Tensor α s}
  {Y : Tensor α s'}
  {i : Fin s.length}
-- given
  (h_s : s = s')
  (h : ∀ k : Fin s[i], X.select i k ≃ Y.select ⟨i, by simp [← h_s]⟩ ⟨k, by simp [← h_s]⟩) :
-- imply
  X.sum i ≃ Y.sum i := by
-- proof
  have h_i := LtVal i
  have h_i' := LtVal.of.Eq (congrArg List.length h_s) i
  sorry


-- created on 2025-11-06
