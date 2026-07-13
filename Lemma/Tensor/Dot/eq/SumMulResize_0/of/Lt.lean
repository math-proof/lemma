import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.SEqSumS.of.SEq
open Bool Tensor Fin


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_k : k < n)
  (A : Tensor α [k])
  (B : Tensor α [n]) :
-- imply
  let A' : Tensor α [n] := A.resize ⟨0, by grind⟩ n
  A @ B = (A' * B).sum 0 := by
-- proof
  simp [Dot.dot]
  unfold Tensor.einsum
  simp
  apply Eq.of.SEq
  apply SEqSumS.of.SEq
  apply SEqMulS.of.SEq.SEq
  ·
    apply SEqResizeS.of.SEq.EqValS.Eq
    .
      grind
    .
      grind
    .
      rfl
  ·
    apply SEqResize_0.of.Eq_Get_0.GtLength_0
    .
      grind
    .
      grind


-- created on 2026-07-13
