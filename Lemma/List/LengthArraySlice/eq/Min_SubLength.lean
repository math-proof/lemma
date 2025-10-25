import Lemma.List.EqLengthArraySlice.of.GeLength_Add
import Lemma.Int.Le_Sub.is.LeAdd
import Lemma.Nat.NotLe.is.Gt
import Lemma.List.EqLengthArraySlice.of.LtLength_Add
import Lemma.Nat.Le.of.Lt
import Lemma.Nat.Add
open List Nat Int


@[main]
private lemma main
  {s : List α}
  {i n : Nat} :
-- imply
  (s.array_slice i n).length = n ⊓ (s.length - i) := by
-- proof
  by_cases h : i + n ≤ s.length
  ·
    rw [EqLengthArraySlice.of.GeLength_Add h]
    simp
    apply Le_Sub.of.LeAdd.left h
  ·
    have h := Gt.of.NotLe h
    rw [EqLengthArraySlice.of.LtLength_Add h]
    simp
    rw [Add.comm]
    apply Le.of.Lt h


-- created on 2025-05-13
