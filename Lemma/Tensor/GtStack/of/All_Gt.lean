import Lemma.Tensor.LtStackS.of.All_Lt
open Tensor


@[path]
private lemma main
  [Preorder α]
  {f g : Fin n → Tensor α s}
-- given
  (h : ∀ i : Fin n, f i > g i) :
-- imply
  [i < n] f i > [i < n] g i := by
-- proof
  exact LtStackS.of.All_Lt h


-- created on 2022-01-01
