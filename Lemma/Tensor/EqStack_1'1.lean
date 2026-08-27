import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
  [One α]
-- given
  (s : List ℕ)
  (n : ℕ) :
-- imply
  [_ < n] (1 : Tensor α s) = 1 := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  conv_rhs => erw [EqGet1_1.fin]
  rw [EqGetStack.fin]
  rfl


-- created on 2026-07-23
