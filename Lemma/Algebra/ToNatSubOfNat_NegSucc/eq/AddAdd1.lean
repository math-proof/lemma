import Lemma.Algebra.SubOfNat_NegSucc.eq.AddAdd1
open Algebra


@[main]
private lemma main
-- given
  (n a : ℕ) :
-- imply
  (OfNat.ofNat a - Int.negSucc n).toNat = a + 1 + n := by
-- proof
  rw [SubOfNat_NegSucc.eq.AddAdd1]
  norm_cast


-- created on 2025-07-18
