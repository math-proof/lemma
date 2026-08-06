import Lemma.Nat.Even.is.Any_Eq_Mul2
import Lemma.Nat.Odd.is.Any_Eq_AddMul2
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Even.is.OddAdd_1 |
| comm | Nat.OddAdd_1.is.Even |
| mp | Nat.OddAdd_1.of.Even |
| mpr | Nat.Even.of.OddAdd_1 |
-/
@[main, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n is even ↔ (n + 1) is odd := by
-- proof
  rw [Even.is.Any_Eq_Mul2]
  rw [Odd.is.Any_Eq_AddMul2]
  simp


-- created on 2025-08-13
