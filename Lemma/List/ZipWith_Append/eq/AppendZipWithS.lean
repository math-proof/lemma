import Lemma.List.EqAppendTake__Drop
import Lemma.List.ZipWith_AppendS.eq.AppendZipWithS.of.EqLengthS
open List


@[main]
private lemma main
  {s s' : List α}
-- given
  (f : α → α → γ) :
-- imply
  List.zipWith f (s.take i ++ s') s = List.zipWith f (s.take i) (s.take i) ++ List.zipWith f s' (s.drop i) := by
-- proof
  have h_s := EqAppendTake__Drop s i
  conv_lhs =>
    arg 3
    rw [← h_s]
  rw [ZipWith_AppendS.eq.AppendZipWithS.of.EqLengthS]
  rfl


-- created on 2026-01-11
