import Lemma.List.GetArraySlice.eq.Get_Add.of.Lt_Length
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Algebra.LtAdd.of.Lt_Sub
import Lemma.Algebra.Lt.of.Lt_Min
open Algebra List


@[main]
private lemma main
  {v : List α}
-- given
  (h : j < (v.slice i n).length) :
-- imply
  have : i + j < v.length := by
    rw [LengthSlice.eq.SubMin] at h
    apply Lt.of.Lt_Min (LtAdd.of.Lt_Sub.left.nat h)
  (v.slice i n)[j] = v[i + j] := by
-- proof
  unfold List.slice
  rw [GetArraySlice.eq.Get_Add.of.Lt_Length]


-- created on 2025-06-07
-- updated on 2025-06-28
