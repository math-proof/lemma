import Lemma.Algebra.Abs.eq.IteLt_0
import Lemma.Algebra.EqNegNeg
import Lemma.Algebra.AbsNeg.eq.Abs
open Algebra


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α} :
-- imply
  |x| = if x > 0 then
    x
  else
    -x := by
-- proof
  have h := Abs.eq.IteLt_0 (x := -x)
  rw [EqNegNeg] at h
  rw [AbsNeg.eq.Abs] at h
  simp at h
  assumption


-- created on 2025-04-18
