import Lemma.Algebra.Sub_NegSucc.eq.AddAdd1
open Algebra


@[main]
private lemma main
-- given
  (n a : ℕ) :
-- imply
  OfNat.ofNat a - Int.negSucc n = a + 1 + n := by
-- proof
  rw [← Sub_NegSucc.eq.AddAdd1]
  aesop


-- created on 2025-07-18
