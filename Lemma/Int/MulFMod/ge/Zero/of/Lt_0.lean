import Lemma.Algebra.Ge_0.of.Le_0.Lt_0
import Lemma.Int.FMod.le.Zero.of.Lt_0
open Algebra Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n.fmod d * d ≥ 0 := by
-- proof
  have := FMod.le.Zero.of.Lt_0 h n
  apply Ge_0.of.Le_0.Lt_0 this h


-- created on 2025-03-23
-- updated on 2025-03-30
