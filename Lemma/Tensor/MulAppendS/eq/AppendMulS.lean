import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Bool.SEqBFnS.of.SEq.SEq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Vector.MulAppendS.eq.AppendMulS
open Bool Tensor Vector


@[main, comm]
private lemma main
  [Mul α]
-- given
  (A C : Tensor α (n :: s))
  (B D : Tensor α (m :: s)) :
-- imply
  (A ++ B) * (C ++ D) = (A * C) ++ (B * D) := by
-- proof
  apply Eq.of.EqDataS
  apply Eq.of.SEq
  apply SEq.of.SEq.SEq (c := (A.data ++ B.data) * (C.data ++ D.data))
  ·
    rw [DataMul.eq.MulDataS]
    exact SEqBFnS.of.SEq.SEq
      (DataAppend.as.AppendDataS A B)
      (DataAppend.as.AppendDataS C D)
      (fun {n} (x y : List.Vector α n) => x * y)
  ·
    rw [MulAppendS.eq.AppendMulS]
    rw [← DataMul.eq.MulDataS, ← DataMul.eq.MulDataS]
    exact DataAppend.as.AppendDataS (A * C) (B * D)


-- created on 2023-06-08
-- updated on 2026-08-24
