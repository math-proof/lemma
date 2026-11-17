module

public import Theorem.List.EqAppendTake__Drop
public import Theorem.List.ZipWith_AppendS.eq.AppendZipWithS.of.Length

public section

open List


public theorem List.ZipWith__Append.eq.AppendZipWithS
  {s s' : List α}
-- given
  (f : α → α → γ) :
-- imply
  List.zipWith f s (s.take i ++ s') = List.zipWith f (s.take i) (s.take i) ++ List.zipWith f (s.drop i) s' := by
-- proof
  conv_lhs =>
    arg 2
    rw [← EqAppendTake__Drop s i]
  rw [ZipWith_AppendS.eq.AppendZipWithS.of.Length]
  rfl


-- created on 2026-01-11
