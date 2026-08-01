import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.LeMulS.of.Gt_0.Le
import Lemma.Nat.Ne.of.Gt
import Lemma.Rat.EqMul_Div.of.Ne_0
import Lemma.Rat.LeDivS.of.Le.Gt_0
open Rat Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.LeMul.is.Le_Div.of.Gt_0 |
| comm | Rat.Le_Div.is.LeMul.of.Gt_0 |
| mp | Rat.Le_Div.of.LeMul.Gt_0 |
| mpr | Rat.LeMul.of.Le_Div.Gt_0 |
| mp.comm | Rat.GeDiv.of.Ge_Mul.Gt_0 |
| mpr.comm | Rat.Ge_Mul.of.GeDiv.Gt_0 |
| comm.is | Rat.Ge_Mul.is.GeDiv.of.Gt_0 |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x > 0)
  (y k : α) :
-- imply
  x * k ≤ y ↔ k ≤ y / x := by
-- proof
  constructor <;>
    intro h_le
  ·
    have := LeDivS.of.Le.Gt_0 h_le h
    rwa [EqDivMul.of.Ne_0.left] at this
    apply Ne.of.Gt h
  ·
    have := LeMulS.of.Gt_0.Le h h_le
    rwa [EqMul_Div.of.Ne_0] at this
    apply Ne.of.Gt h


-- created on 2025-12-11
