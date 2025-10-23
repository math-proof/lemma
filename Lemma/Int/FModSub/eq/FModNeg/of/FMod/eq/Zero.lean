import Lemma.Int.FModAdd.eq.FMod.of.FMod.eq.Zero
import Lemma.Int.Sub.eq.Add_Neg
open Int


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
  rwa [Add_Neg.eq.Sub] at this


-- created on 2025-03-30
