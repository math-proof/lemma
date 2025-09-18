import Lemma.Algebra.FloorDiv.eq.Zero.of.Lt
import Lemma.Algebra.LtCoeS.is.Lt
import Lemma.Algebra.LtMod.of.Ne_0
open Algebra


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
    apply LtCoeS.of.Lt.nat
    apply LtMod.of.Ne_0 h


-- created on 2025-07-07
