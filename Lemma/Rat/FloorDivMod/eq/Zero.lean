import Lemma.Nat.FloorDiv.eq.Zero.of.Lt
import Lemma.Nat.LtCoeS.is.Lt
import Lemma.Nat.LtMod.of.Ne_0
open Nat


@[main]
private lemma main
-- given
  (n k : ℕ) :
-- imply
  ⌊(k % n : ℕ) / (n : ℚ)⌋ = 0 := by
-- proof
  by_cases h : n = 0
  ·
    subst h
    simp
  ·
    apply FloorDiv.eq.Zero.of.Lt
    apply LtCoeS.of.Lt
    apply LtMod.of.Ne_0 h


-- created on 2025-07-07
