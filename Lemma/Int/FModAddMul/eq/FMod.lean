import Lemma.Algebra.FMod.eq.Zero.of.Any_Eq_Mul
import Lemma.Int.FModAdd.eq.FMod.of.FMod.eq.Zero
open Algebra Int


@[main]
private lemma main
  {d q r : ℤ} :
-- imply
  (q * d + r).fmod d = r.fmod d := by
-- proof
  apply FModAdd.eq.FMod.of.FMod.eq.Zero
  apply FMod.eq.Zero.of.Any_Eq_Mul
  use q


-- created on 2025-03-30
