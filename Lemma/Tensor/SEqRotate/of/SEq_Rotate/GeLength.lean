import stdlib.SEq
import Lemma.Tensor.SEqRotateRotate.of.GeLength
import Lemma.Tensor.SEqRotateS.of.SEq
import Lemma.Nat.EqSub_Sub.of.Ge
open Tensor Nat


@[main]
private lemma main
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h_i : s.length ≥ i)
  (h : X ≃ Y.rotate (s.length - i)) :
-- imply
  X.rotate i ≃ Y := by
-- proof
  have h_s := h.left
  have h_length := congrArg List.length h_s
  simp at h_length
  have h := SEqRotateS.of.SEq h i
  have := SEqRotateRotate.of.GeLength (i := s.length - i) (by grind) Y
  rw [← h_length] at this
  rw [EqSub_Sub.of.Ge (by grind)] at this
  apply h.trans this


-- created on 2025-10-19
