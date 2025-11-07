import Lemma.Rat.FloorDiv.eq.Zero.of.Lt
import Lemma.Nat.LtCoeS.is.Lt
import Lemma.Nat.LtMod.of.Ne_0
open Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (n k : ℕ) :
-- imply
  ⌊(k % n : ℕ) / (n : α)⌋ = 0 := by
-- proof
  if h : n = 0 then
    subst h
    simp
  else
    apply FloorDiv.eq.Zero.of.Lt
    apply LtCoeS.of.Lt
    apply LtMod.of.Ne_0 h


-- created on 2025-07-07
