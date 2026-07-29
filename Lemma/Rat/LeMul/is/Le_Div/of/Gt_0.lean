import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.LeMulS.of.Gt_0.Le
import Lemma.Nat.Ne.of.Gt
import Lemma.Rat.EqMul_Div.of.Ne_0
import Lemma.Rat.LeDivS.of.Le.Gt_0
open Rat Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.LeDiv.is.Le_Mul.of.Gt_0 |
| comm | Rat.Le_Mul.is.LeDiv.of.Gt_0 |
| mp   | Rat.Le_Mul.of.LeDiv.Gt_0 |
| mpr  | Rat.LeDiv.of.Le_Mul.Gt_0 |
| mp.comm | Rat.GtMul.of.Gt_Div.Gt_0 |
| mpr.comm | Rat.Gt_Div.of.GtMul.Gt_0 |
| comm.is | Rat.Gt_Div.is.GtMul.of.Gt_0 |
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
