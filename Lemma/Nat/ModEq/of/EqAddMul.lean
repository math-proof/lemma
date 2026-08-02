import Lemma.Nat.Mod.of.EqAddMul
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.ModEq.of.EqAddMul |
| comm 1 | Nat.ModEq.of.Eq_AddMul |
-/
@[main, comm 1]
private lemma main
  {n d q r : ℕ}
-- given
  (h : q * d + r = n) :
-- imply
  r ≡ n [MOD d] := by
-- proof
  simp [Nat.ModEq, Mod.of.EqAddMul h]


-- created on 2026-08-02
