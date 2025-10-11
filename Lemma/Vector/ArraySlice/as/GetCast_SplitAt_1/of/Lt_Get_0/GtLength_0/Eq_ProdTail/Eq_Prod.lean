import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Vector.GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Vector.SEqArraySliceS.of.SEq.Eq.Eq
import Lemma.Nat.EqMulS.of.Eq
open Vector List Bool Nat


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (h_m : m = s.prod)
  (h_n : n = s.tail.prod)
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (v : List.Vector α m) :
-- imply
  let h : List.Vector α m = List.Vector α s.prod := by rw [h_m]
  have : i < (s.take 1).prod := by rwa [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  v.array_slice (i * n) n ≃ ((cast h v).splitAt 1)[i] := by
-- proof
  intro h h_i'
  have := GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0 h_s h_i (cast h v)
  apply SEq.of.SEq.SEq _ this
  apply SEqArraySliceS.of.SEq.Eq.Eq
  ·
    apply EqMulS.of.Eq.left h_n
  ·
    assumption
  ·
    aesop


-- created on 2025-07-11
