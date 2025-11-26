import Lemma.List.EraseIdxAppend.eq.AppendEraseIdx.of.Lt_Length
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > d + i) :
-- imply
  (s.rotate d).eraseIdx i = (s.drop d).eraseIdx i ++ s.take d := by
-- proof
  rw [Rotate.eq.AppendDrop__Take.of.GeLength (by omega)]
  rw [EraseIdxAppend.eq.AppendEraseIdx.of.Lt_Length]
  simp
  omega


-- created on 2025-10-31
