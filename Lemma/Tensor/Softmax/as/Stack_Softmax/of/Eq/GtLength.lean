import Lemma.Tensor.EqStackSUFnGet.of.Eq
import Lemma.Tensor.Softmax.eq.Stack_Softmax.of.GtLength
open Tensor


@[main]
private lemma main
  [Exp α]
  {d : ℕ}
-- given
  (h₀ : n = m)
  (h₁ : s.length > d)
  (X : Tensor α (n :: s)) :
-- imply
  have : X.length = m := by aesop
  X.softmax (d + 1) ≃ [i < m] (X[i].softmax d) := by
-- proof
  rw [Softmax.eq.Stack_Softmax.of.GtLength h₁]
  apply EqStackSUFnGet.of.Eq h₀ id (fun X => X.softmax d)


-- created on 2025-11-30
