import Lemma.Nat.Even.is.OddAdd_1
import Lemma.Nat.Odd.is.NotEven
import Lemma.Nat.NotOdd.is.Even
import Lemma.Bool.Iff.is.IffNotS
open Nat Bool


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.EvenAdd_1.is.Odd |
| comm | Nat.Odd.is.EvenAdd_1 |
| mp | Nat.Odd.of.EvenAdd_1 |
| mpr | Nat.EvenAdd_1.of.Odd |
-/
@[main, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  (n + 1) is even ↔ n is odd := by
-- proof
  rw [Even.is.NotOdd]
  rw [← IffNotS.of.Iff (Even.is.OddAdd_1 n)]
  rw [Odd.is.NotEven]


-- created on 2026-08-16
