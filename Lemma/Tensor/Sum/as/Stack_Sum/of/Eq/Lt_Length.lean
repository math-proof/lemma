import Lemma.Tensor.Sum.eq.Stack_Sum.of.Lt_Length
import Lemma.Tensor.EqStackSUFnGet.of.Eq
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (h₀ : n = m)
  (h₁ : dim < s.length)
  (X : Tensor α (n :: s)) :
-- imply
  have : X.length = m := by aesop
  X.sum (dim + 1) ≃ [i < m] (X[i].sum dim) := by
-- proof
  rw [Sum.eq.Stack_Sum.of.Lt_Length h₁]
  apply EqStackSUFnGet.of.Eq h₀ (fun s => s.eraseIdx dim) (fun X => X.sum dim)


-- created on 2025-06-27
-- updated on 2025-07-13
