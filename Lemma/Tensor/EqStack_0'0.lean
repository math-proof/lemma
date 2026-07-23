import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
  [Zero α]
-- given
  (s : List ℕ)
  (n : ℕ) :
-- imply
  [_ < n] (0 : Tensor α s) = 0 := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  simp [EqGet0_0.fin]
  rw [EqGetStack.fn.fin]
  rfl


-- created on 2026-07-23
