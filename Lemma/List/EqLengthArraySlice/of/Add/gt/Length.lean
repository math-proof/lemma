import Lemma.Algebra.Ge.of.Gt
import Lemma.List.EqLengthArraySlice.of.Add.ge.Length
open Algebra List


@[main]
private lemma main
  {s : List α}
  {i n : Nat}
-- given
  (h : i + n > s.length) :
-- imply
  (s.array_slice i n).length = s.length - i := by
-- proof
  have h := Ge.of.Gt h
  apply EqLengthArraySlice.of.Add.ge.Length h


-- created on 2025-05-13
