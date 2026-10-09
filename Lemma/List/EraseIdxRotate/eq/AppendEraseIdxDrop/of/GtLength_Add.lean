import Lemma.List.EraseIdxAppend.eq.AppendEraseIdx.of.GtLength
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
open List


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length > d + i) :
-- imply
  (s.rotate d).eraseIdx i = (s.drop d).eraseIdx i ++ s.take d := by
-- proof
  rw [Rotate.eq.AppendDrop__Take.of.GeLength (by omega)]
  rw [EraseIdxAppend.eq.AppendEraseIdx.of.GtLength]
  simp
  omega


-- created on 2025-10-31
