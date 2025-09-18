import Lemma.Algebra.LengthArraySlice.eq.Min_SubLength
import Lemma.Algebra.SubMin.eq.MinSubS
open Algebra


@[main]
private lemma main
-- given
  (s : List α)
  (i j : Nat) :
-- imply
  (s.slice i j).length = j ⊓ s.length - i := by
-- proof
  unfold List.slice
  rw [LengthArraySlice.eq.Min_SubLength]
  rw [MinSubS.eq.SubMin.nat]


-- created on 2025-05-13
-- updated on 2025-05-16
