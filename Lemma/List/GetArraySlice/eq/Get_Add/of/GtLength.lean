import Lemma.List.LengthArraySlice.eq.Min_SubLength
import Lemma.Nat.Lt.of.Lt_Min
import Lemma.Nat.LtAdd.of.Lt_Sub
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : j < (s.array_slice i n).length):
-- imply
  have : i + j < s.length := by
    rw [LengthArraySlice.eq.Min_SubLength] at h
    apply LtAdd.of.Lt_Sub.left (Lt.of.Lt_Min h)
  (s.array_slice i n)[j] = s[i + j] := by
-- proof
  unfold List.array_slice
  simp_all


-- created on 2025-06-07
-- updated on 2025-06-28
