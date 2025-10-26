import Lemma.List.EqLengthArraySlice.of.LtLength_Add
import Lemma.List.EqLengthArraySlice.of.GeLength_Add
open List


@[main]
private lemma main
  {s : List α}
  {i n : Nat} :
-- imply
  (s.array_slice i n).length = n ⊓ (s.length - i) := by
-- proof
  by_cases h : i + n ≤ s.length
  ·
    rw [EqLengthArraySlice.of.GeLength_Add]
    repeat grind
  ·
    rw [EqLengthArraySlice.of.LtLength_Add]
    repeat grind


-- created on 2025-05-13
