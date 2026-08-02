import Lemma.Nat.Mod.of.Eq
import Lemma.Nat.ModAddMul.eq.Mod
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Mod.of.EqAddMul |
| comm 1 | Nat.Mod.of.Eq_AddMul |
-/
@[main, comm 1]
private lemma main
  {n d q r : ℕ}
-- given
  (h : q * d + r = n) :
-- imply
  r % d = n % d := by
-- proof
  rw [← Mod.of.Eq h d, ModAddMul.eq.Mod]


-- created on 2026-08-02
