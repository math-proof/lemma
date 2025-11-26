import Lemma.Tensor.Sum.eq.Stack_Sum.of.GtLength
import Lemma.Tensor.EqStackSUFnGet.of.Eq
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h₀ : n = m)
  (h₁ : d < s.length)
  (X : Tensor α (n :: s)) :
-- imply
  have : X.length = m := by aesop
  X.sum (d + 1) ≃ [i < m] (X[i].sum d) := by
-- proof
  rw [Sum.eq.Stack_Sum.of.GtLength h₁]
  apply EqStackSUFnGet.of.Eq h₀ (fun s => s.eraseIdx d) (fun X => X.sum d)


-- created on 2025-06-27
-- updated on 2025-07-13
