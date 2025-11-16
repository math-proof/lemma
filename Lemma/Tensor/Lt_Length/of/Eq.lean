import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.List.LengthCons.gt.Zero
open Tensor List


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i : Fin A.length) :
-- imply
  i < B.length := by
-- proof
  have h_i := i.isLt
  match s with
  | [] =>
    contradiction
  | n :: s =>
    have h_s := h.left
    have := LengthCons.gt.Zero n s
    rw [h_s] at this
    rw [Length.eq.Get_0.of.GtLength_0 this]
    simp [← h_s]
    simp [Tensor.length]


-- created on 2025-07-24
