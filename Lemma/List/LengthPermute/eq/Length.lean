import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.LengthCons.eq.Add1Length
import Lemma.List.LengthSlice.eq.SubMin
open List

/--
you're supposed to use the tactic `simp` instead of calling this lemma directly
-/
@[main, simp]
private lemma main
-- given
  (s : List α)
  (i : Fin s.length)
  (d : ℤ) :
-- imply
  (s.permute i d).length = s.length := by
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
