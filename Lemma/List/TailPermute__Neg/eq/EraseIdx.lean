import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TailRotate.eq.Take.of.EqLength_Add_1
import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (d : Fin s.length) :
-- imply
  (s.permute d (-d)).tail = s.eraseIdx d := by
-- proof
  rw [Permute__Neg.eq.Append_AppendRotateDropTake]
  rw [TailAppend.eq.AppendTail.of.GtLength_0]
  ·
    simp [EraseIdx.eq.Append_Drop_Add_1]
    rw [TailRotate.eq.Take.of.EqLength_Add_1]
    ·
      rw [TakeTake.eq.Take.of.Ge (by omega)]
    ·
      simp
      linarith [d.isLt]
  ·
    simp
    linarith [d.isLt]


-- created on 2025-11-24
