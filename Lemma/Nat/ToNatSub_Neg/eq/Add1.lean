import Lemma.Nat.Add
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
open Nat


@[main]
private lemma main
-- given
  (d : ℕ) :
-- imply
  (1 - -(d : ℤ)).toNat = 1 + d :=
-- proof
  Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d


-- created on 2025-12-02
