import Lemma.Nat.Add
import Lemma.Nat.ToNatSub_Neg.eq.Add1
open Nat


@[main]
private lemma main
-- given
  (d : ℕ) :
-- imply
  (1 - -(d : ℤ)).toNat = d + 1 := by
-- proof
  have h_toNat := ToNatSub_Neg.eq.Add1 d
  rwa [Add.comm] at h_toNat


-- created on 2025-12-02
