import Lemma.Int.Mod.ge.Zero.of.Ne_0
import Lemma.Nat.Ne.of.Gt
open Nat Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n % d ≥ 0 := by
-- proof
  apply Mod.ge.Zero.of.Ne_0
  apply Ne.of.Gt
  assumption


-- created on 2025-03-18
