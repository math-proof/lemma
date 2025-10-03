import Lemma.List.EqLengthArraySlice.of.Add.le.Length
import Lemma.Algebra.Le_Sub.is.LeAdd
import Lemma.Algebra.NotLe.is.Gt
import Lemma.List.EqLengthArraySlice.of.Add.gt.Length
import Lemma.Algebra.Le.of.Lt
import Lemma.Algebra.Add
open Algebra List


@[main]
private lemma main
  {s : List α}
  {i n : Nat} :
-- imply
  (s.array_slice i n).length = n ⊓ (s.length - i) := by
-- proof
  by_cases h : i + n ≤ s.length
  ·
    rw [EqLengthArraySlice.of.Add.le.Length h]
    simp
    apply Le_Sub.of.LeAdd.left.nat h
  ·
    have h := Gt.of.NotLe h
    rw [EqLengthArraySlice.of.Add.gt.Length h]
    simp
    rw [Add.comm]
    apply Le.of.Lt h


-- created on 2025-05-13
