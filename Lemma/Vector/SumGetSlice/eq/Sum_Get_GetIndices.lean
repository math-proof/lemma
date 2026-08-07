import Lemma.Vector.SumMapRange.eq.Sum_UFn
import Lemma.Vector.GetSlice.eq.MapRange
open Vector


@[main]
private lemma main
  [AddCommMonoid α]
  {N : ℕ}
-- given
  (v : List.Vector α N)
  (s : Slice) :
-- imply
  (v.getSlice s).sum = ∑ i : Fin (s.length N), v[(List.Vector.indices s N)[i]] := by
-- proof
  rw [GetSlice.eq.MapRange]
  rw [SumMapRange.eq.Sum_UFn]


-- created on 2023-05-30
-- updated on 2026-08-07
