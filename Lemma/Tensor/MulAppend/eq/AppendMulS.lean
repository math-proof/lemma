import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Tensor.Mul.eq.Mul_GetData_0
import Lemma.Vector.MulAppend.eq.AppendMulS
import Lemma.Vector.SEqMulS.of.SEq
open Bool Tensor Vector


@[main]
private lemma scalar
  [Mul α]
-- given
  (A : Tensor α (n :: s))
  (B : Tensor α (m :: s))
  (c : α) :
-- imply
  (A ++ B) * c = (A * c) ++ (B * c) := by
-- proof
  apply Eq.of.EqDataS
  apply Eq.of.SEq
  apply SEq.of.SEq.SEq (c := (A.data ++ B.data) * c)
  ·
    rw [DataMul.eq.MulData]
    exact SEqMulS.of.SEq (DataAppend.as.AppendDataS A B) c
  ·
    rw [MulAppend.eq.AppendMulS]
    rw [← DataMul.eq.MulData, ← DataMul.eq.MulData]
    exact DataAppend.as.AppendDataS (A * c) (B * c)


@[main]
private lemma main
  [Mul α]
-- given
  (A : Tensor α (n :: s))
  (B : Tensor α (m :: s))
  (C : Tensor α []) :
-- imply
  (A ++ B) * C = (A * C) ++ (B * C) := by
-- proof
  rw [Mul.eq.Mul_GetData_0]
  rw [Mul.eq.Mul_GetData_0 (X := A)]
  rw [Mul.eq.Mul_GetData_0 (X := B)]
  apply scalar


-- created on 2021-12-30
-- updated on 2026-08-24
