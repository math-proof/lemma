import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Int.EqToNat_0.of.Lt_0
import Lemma.Int.LeToNat.is.Le
import Lemma.Nat.LtCoeS.is.Lt
import Lemma.Nat.NotLt.of.Ge
import Lemma.Nat.NotLe.is.Gt
import Lemma.Set.In_Ico.is.Le.Lt
import sympy.sets.sets
open Int Set Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.In_Ico.is.In_IcoToNatS |
| comm | Int.In_IcoToNatS.is.In_Ico |
| mp | Int.In_IcoToNatS.of.In_Ico |
| mpr | Int.In_Ico.of.In_IcoToNatS |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℕ)
  (a b : ℤ) :
-- imply
  ↑x ∈ Ico a b ↔ x ∈ Ico a.toNat b.toNat := by
-- proof
  grind


-- created on 2026-08-08
