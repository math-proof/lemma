import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Bool.SEqBFnS.of.SEq.SEq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Vector.AddAppendS.eq.AppendAddS
open Bool Tensor Vector


@[main, comm]
private lemma main
  [Add α]
-- given
  (A C : Tensor α (n :: s))
  (B D : Tensor α (m :: s)) :
-- imply
  (A ++ B) + (C ++ D) = (A + C) ++ (B + D) := by
-- proof
  apply Eq.of.EqDataS
  apply Eq.of.SEq
  apply SEq.of.SEq.SEq (c := (A.data ++ B.data) + (C.data ++ D.data))
  ·
    rw [DataAdd.eq.AddDataS]
    exact SEqBFnS.of.SEq.SEq
      (DataAppend.as.AppendDataS A B)
      (DataAppend.as.AppendDataS C D)
      (fun {n} (x y : List.Vector α n) => x + y)
  ·
    rw [AddAppendS.eq.AppendAddS]
    rw [← DataAdd.eq.AddDataS, ← DataAdd.eq.AddDataS]
    exact DataAppend.as.AppendDataS (A + C) (B + D)


-- created on 2018-08-04
-- updated on 2026-08-24
