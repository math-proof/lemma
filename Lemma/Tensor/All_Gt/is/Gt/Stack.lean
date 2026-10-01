import Lemma.Tensor.All_Gt.of.Gt.Stack
import Lemma.Tensor.GtStack.of.All_Gt
open Tensor


@[main]
private lemma main
  [Preorder α]
  {f g : Fin n → Tensor α s} :
-- imply
  (∀ i : Fin n, f i > g i) ↔ [i < n] f i > [i < n] g i := by
-- proof
  exact ⟨GtStack.of.All_Gt, All_Gt.of.Gt.Stack⟩


-- created on 2022-03-31
