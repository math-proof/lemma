import Lemma.Nat.Add
import Lemma.Nat.ToNatSub_Neg.eq.Add
open Nat


@[path]
private lemma main
-- given
  (d : ℕ) :
-- imply
  (1 - -(d : ℤ)).toNat = 1 + d := by
-- proof
  simpa using ToNatSub_Neg.eq.Add 1 d


-- created on 2025-12-02
-- updated on 2026-11-21
