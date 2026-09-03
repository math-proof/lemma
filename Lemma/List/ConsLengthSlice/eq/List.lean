import Lemma.List.LengthSlice.eq.Min
import Lemma.List.LengthSlice.eq.SubMin
import stdlib.Slice
open List


@[main]
private lemma head
-- given
  (n : ℕ) :
-- imply
  (⟨0, n, 1⟩ : Slice).length (n + n) :: [n + n].tail = [n] := by
-- proof
  simp [LengthSlice.eq.Min]


@[main]
private lemma tail
-- given
  (n : ℕ) :
-- imply
  (⟨n, n + n, 1⟩ : Slice).length (n + n) :: [n + n].tail = [n] := by
-- proof
  simp
  simpa [Int.natCast_add] using LengthSlice.eq.SubMin (n + n) (n + n) n


-- created on 2026-09-03
