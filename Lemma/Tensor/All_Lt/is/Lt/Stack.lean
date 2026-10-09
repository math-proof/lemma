import Lemma.Tensor.All_Lt.of.Lt.Stack
import Lemma.Tensor.LtStack.of.All_Lt
open Tensor


@[path]
private lemma main
  [Preorder α]
  {f g : Fin n → Tensor α s} :
-- imply
  (∀ i : Fin n, f i < g i) ↔ [i < n] f i < [i < n] g i := by
-- proof
  exact ⟨LtStack.of.All_Lt, All_Lt.of.Lt.Stack⟩


-- created on 2022-03-31
