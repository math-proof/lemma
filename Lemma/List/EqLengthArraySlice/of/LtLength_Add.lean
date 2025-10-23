import Lemma.Nat.Ge.of.Gt
import Lemma.List.EqLengthArraySlice.of.LeLength_Add
open List Nat


@[main]
private lemma main
  {s : List α}
  {i d : ℕ}
-- given
  (h : s.length < i + d) :
-- imply
  (s.array_slice i d).length = s.length - i := by
-- proof
  have h := Ge.of.Gt h
  apply EqLengthArraySlice.of.LeLength_Add h


-- created on 2025-05-13
