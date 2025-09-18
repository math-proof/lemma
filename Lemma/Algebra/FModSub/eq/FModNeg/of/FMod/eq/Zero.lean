import Lemma.Algebra.FModAdd.eq.FMod.of.FMod.eq.Zero
import Lemma.Algebra.Sub.eq.Add_Neg
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n.fmod d = 0)
  (m : ℤ) :
-- imply
  (n - m).fmod d = (-m).fmod d := by
-- proof
  have := FModAdd.eq.FMod.of.FMod.eq.Zero h (-m)
  rw [Add_Neg.eq.Sub] at this
  assumption


-- created on 2025-03-30
