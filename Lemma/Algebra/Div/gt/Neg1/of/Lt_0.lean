import Lemma.Algebra.Mod.lt.Neg.of.Lt_0
import Lemma.Algebra.GtDivS.of.Lt.Lt_0
import Lemma.Algebra.DivNeg.eq.Neg1.of.Lt_0
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  (n % d : ℤ) / (d : ℚ) > -1 := by
-- proof
  have := Mod.lt.Neg.of.Lt_0 h n
  have : ((n % d) : ℤ) < ((-d : ℤ) : ℚ) := by norm_cast
  have h : (d : ℚ) < 0 := by simp [h]
  have := GtDivS.of.Lt.Lt_0 this h
  simp at this
  rwa [DivNeg.eq.Neg1.of.Lt_0 h] at this


-- created on 2025-03-20
-- updated on 2025-03-29
