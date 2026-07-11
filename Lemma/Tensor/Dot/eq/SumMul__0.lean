import Lemma.Bool.HEq.of.SEq
import Lemma.Fin.Eq_0
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.HeadDataSum.eq.SumData
import Lemma.Tensor.SEqDataS.of.SEq
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.SEqMulS.of.SEq.SEq
open Bool Fin Tensor Vector


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [n])
  (B : Tensor α [n]) :
-- imply
  A @ B = (A * B).sum 0 := by
-- proof
  simp [Dot.dot]
  unfold einsum
  simp
  apply Eq.of.EqDataS
  simp
  apply @Vector.Eq.of.All_EqGetS.fin
  intro i
  have h_i := Eq_0 i
  subst h_i
  simp [HeadDataSum.eq.SumData]
  rw [DataMul.eq.MulDataS]
  congr 1
  ·
    simp
  ·
    apply HEq.of.SEq
    apply SEqMulS.of.SEq.SEq <;>
    ·
      apply SEqDataS.of.SEq
      apply SEqResize_0.of.Eq_Get_0.GtLength_0
      ·
        simp
      ·
        simp


-- created on 2026-07-11
