import Lemma.Nat.Mod.of.EqAddMul
open Nat


@[main]
private lemma main
  {d q r q' r': ℕ}
-- given
  (h : q * d + r = q' * d + r') :
-- imply
  r ≡ r' [MOD d] := by
-- proof
  simp [ModEq, Mod.of.EqAddMul h]


-- created on 2026-08-02
