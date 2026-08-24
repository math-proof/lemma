import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Tensor.Dot.eq.TensorDotDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Dot.eq.SumMul
import Lemma.Vector.DotAppendS.eq.AddDotS
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.SEqMulS.of.SEq.SEq
import Lemma.Vector.Sum.of.SEq
open Tensor Vector


@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A C : Tensor α [n])
  (B D : Tensor α [m]) :
-- imply
  (A ++ B) @ (C ++ D) = id (α := Tensor α []) (A @ C) + id (α := Tensor α []) (B @ D) := by
-- proof
  simp only [id]
  rw [Dot.eq.TensorDotDataS]
  rw [Dot.eq.TensorDotDataS A C]
  rw [Dot.eq.TensorDotDataS B D]
  apply Eq.of.EqDataS
  apply Eq.of.All_EqGetS.fin
  intro i
  fin_cases i
  simp [List.Vector.get]
  change (A ++ B).data @ (C ++ D).data = A.data @ C.data + B.data @ D.data
  rw [AddDotS.eq.DotAppendS A.data C.data B.data D.data]
  rw [Dot.eq.SumMul]
  rw [Dot.eq.SumMul (A.data ++ B.data) (C.data ++ D.data)]
  apply Sum.of.SEq
  exact SEqMulS.of.SEq.SEq (DataAppend.as.AppendDataS A B) (DataAppend.as.AppendDataS C D)


-- created on 2026-08-23
-- updated on 2026-08-24
