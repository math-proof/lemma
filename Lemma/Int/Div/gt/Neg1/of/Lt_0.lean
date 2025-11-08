import Lemma.Int.Mod.lt.Neg.of.Lt_0
import Lemma.Rat.GtDivS.of.Lt.Lt_0
import Lemma.Rat.DivNeg.eq.Neg1.of.Lt_0
open Int Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  (n % d : ℤ) / (d : α) > -1 := by
-- proof
  have := Mod.lt.Neg.of.Lt_0 h n
  have : ((n % d) : ℤ) < ((-d : ℤ) : α) := by norm_cast
  have h : (d : α) < 0 := by simp [h]
  have := GtDivS.of.Lt.Lt_0 this h
  simp at this
  rwa [DivNeg.eq.Neg1.of.Lt_0 h] at this


-- created on 2025-03-20
-- updated on 2025-03-29
