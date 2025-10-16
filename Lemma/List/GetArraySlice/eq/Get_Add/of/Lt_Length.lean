import Lemma.List.LengthArraySlice.eq.Min_SubLength
import Lemma.Algebra.Lt.of.Lt_Min
import Lemma.Nat.LtAdd.of.Lt_Sub
open Algebra List Nat


@[main]
private lemma main
  {v : List α}
-- given
  (h : j < (v.array_slice i n).length):
-- imply
  have : i + j < v.length := by
    rw [LengthArraySlice.eq.Min_SubLength] at h
    apply LtAdd.of.Lt_Sub.left (Lt.of.Lt_Min h)
  (v.array_slice i n)[j] = v[i + j] := by
-- proof
  unfold List.array_slice
  simp_all


-- created on 2025-06-07
-- updated on 2025-06-28
