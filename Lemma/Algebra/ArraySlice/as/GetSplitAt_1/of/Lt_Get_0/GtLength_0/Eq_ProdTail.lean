import Lemma.Algebra.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Logic.SEq.of.SEq.SEq
import Lemma.Algebra.GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0
import Lemma.Algebra.EqArraySliceS.of.Eq.Eq
open Algebra Logic


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (h_n : n = s.tail.prod)
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (v : List.Vector α s.prod) :
-- imply
  have : i < (s.take 1).prod := by rwa [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  v.array_slice (i * n) n ≃ (v.splitAt 1)[i] := by
-- proof
  intro h_i'
  have := GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0 h_s h_i v
  apply SEq.of.SEq.SEq _ this
  apply EqArraySliceS.of.Eq.Eq <;>
    rw [h_n]


-- created on 2025-07-12
