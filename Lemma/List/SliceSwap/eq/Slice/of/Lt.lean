import Lemma.List.SliceAppend.eq.Take_Sub.of.Eq_Length
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.List.Cons.eq.Append
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.EqTakeAppend.of.Eq_Length
import Lemma.Nat.Le.of.Lt.Lt
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.EqMin.of.Lt
open List Nat


@[main]
private lemma main
  {i j : ℕ}
-- given
  (h : i < j)
  (a : List α) :
-- imply
  (a.swap i j).slice (i + 1) j = a.slice (i + 1) j := by
-- proof
  unfold List.swap
  split_ifs with h_eq h_j
  ·
    rfl
  ·
    rw [Cons.eq.Append a[j]]
    rw [Append_Append.eq.AppendAppend]
    rw [AppendAppend.eq.Append_Append]
    rw [SliceAppend.eq.Take_Sub.of.Eq_Length]
    ·
      rw [EqTakeAppend.of.Eq_Length]
      rw [LengthSlice.eq.SubMin]
      rw [EqMin.of.Lt h_j]
    ·
      rw [LengthAppend.eq.AddLengthS]
      rw [LengthTake.eq.Min_Length]
      simp
      apply Le.of.Lt.Lt h h_j
  ·
    rfl


-- created on 2025-05-17
-- updated on 2025-05-18
