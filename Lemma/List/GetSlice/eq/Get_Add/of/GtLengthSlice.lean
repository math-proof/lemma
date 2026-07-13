import Lemma.List.GetArraySlice.eq.Get_Add.of.GtLength
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.Nat.Lt.of.Lt_Min
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : j < (s.slice i n).length) :
-- imply
  have : i + j < s.length := by
    rw [LengthSlice.eq.SubMin] at h
    apply Lt.of.Lt_Min (LtAdd.of.Lt_Sub.left h)
  (s.slice i n)[j] = s[i + j] := by
-- proof
  unfold List.slice
  rw [GetArraySlice.eq.Get_Add.of.GtLength]


-- created on 2025-06-07
-- updated on 2025-06-28
