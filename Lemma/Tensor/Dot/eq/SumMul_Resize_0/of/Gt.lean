import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.SEqSumS.of.SEq
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_k : n > k)
  (A : Tensor α [n])
  (B : Tensor α [k]) :
-- imply
  let B' : Tensor α [n] := B.resize ⟨0, by grind⟩ n
  A @ B = (A * B').sum 0 := by
-- proof
  simp [Dot.dot]
  unfold Tensor.einsum
  simp
  apply Eq.of.SEq
  apply SEqSumS.of.SEq
  apply SEqMulS.of.SEq.SEq
  ·
    apply SEqResize_0.of.Eq_Get_0.GtLength_0
    ·
      grind
    ·
      grind
  ·
    apply SEqResizeS.of.SEq.EqValS.Eq
    ·
      grind
    ·
      grind
    ·
      rfl


-- created on 2026-07-13
