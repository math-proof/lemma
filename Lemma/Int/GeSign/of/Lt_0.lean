import Lemma.Int.Sign.eq.Neg1.of.Lt_0
import Lemma.Nat.Le_Sub_1.of.Lt
open Nat Int


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d < 0) :
-- imply
  sign d ≥ d := by
-- proof
  have := Sign.eq.Neg1.of.Lt_0 h
  rw [this]
  have := Le_Sub_1.of.Lt h
  simp_all


-- created on 2025-03-30
