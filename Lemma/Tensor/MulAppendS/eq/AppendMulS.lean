import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Bool.SEqBFnS.of.SEq.SEq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataAppend.as.AppendDataS
open Bool Tensor Vector


private lemma appendData
  [Mul α]
-- given
  (a c : List.Vector α n)
  (b d : List.Vector α m) :
-- imply
  (a ++ b) * (c ++ d) = a * c ++ b * d := by
-- proof
  apply Subtype.ext
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨c, hc⟩ := c
  obtain ⟨d, hd⟩ := d
  apply List.zipWith_append
  rw [ha, hc]

/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.MulAppendS.eq.AppendMulS |
| comm | Tensor.AppendMulS.eq.MulAppendS |
-/
@[path, comm]
private lemma main
  [Mul α]
-- given
  (A C : Tensor α (n :: s))
  (B D : Tensor α (m :: s)) :
-- imply
  (A ++ B) * (C ++ D) = A * C ++ B * D := by
-- proof
  apply Eq.of.EqDataS
  apply Eq.of.SEq
  apply SEq.of.SEq.SEq (c := (A.data ++ B.data) * (C.data ++ D.data))
  ·
    rw [DataMul.eq.MulDataS]
    apply SEqBFnS.of.SEq.SEq
      (DataAppend.as.AppendDataS A B)
      (DataAppend.as.AppendDataS C D)
      (fun {n} (x y : List.Vector α n) => x * y)
  ·
    rw [appendData]
    rw [← DataMul.eq.MulDataS, ← DataMul.eq.MulDataS]
    exact DataAppend.as.AppendDataS (A * C) (B * D)


-- created on 2023-06-08
-- updated on 2026-11-20
