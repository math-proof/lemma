import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.LengthCons.eq.Add1Length
import Lemma.List.LengthSlice.eq.SubMin
open List


@[main, simp]
private lemma main
-- given
  (a : List α)
  (i : Fin a.length)
  (d : ℤ) :
-- imply
  (a.permute i d).length = a.length := by
-- proof
  unfold List.permute
  split <;>
  ·
    repeat rw [LengthAppend.eq.AddLengthS]
    rw [LengthCons.eq.Add1Length]
    rw [LengthSlice.eq.SubMin]
    grind


-- created on 2025-06-07
-- updated on 2025-10-25
