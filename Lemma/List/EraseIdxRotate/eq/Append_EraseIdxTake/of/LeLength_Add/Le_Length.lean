import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.Nat.SubAdd.eq.Sub_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h_d : d ≤ s.length)
  (h : s.length ≤ i + d) :
-- imply
  (s.rotate d).eraseIdx i = s.drop d ++ (s.take d).eraseIdx (i + d - s.length) := by
-- proof
  rw [Rotate.eq.AppendDrop__Take.of.Le_Length (by omega)]
  rw [EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length (by simpa)]
  simp
  rw [Sub_Sub.eq.SubAdd.of.Ge h_d]


-- created on 2025-10-31
