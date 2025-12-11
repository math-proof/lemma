import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.LeMulS.of.Gt_0.Le
import Lemma.Nat.Ne.of.Gt
import Lemma.Rat.EqMul_Div.of.Ne_0
import Lemma.Rat.LeDivS.of.Le.Gt_0
open Rat Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.LeDiv.is.Le\_Mul.of.Gt\_0 |
| comm | Rat.Le\_Mul.is.LeDiv.of.Gt\_0 |
| mp   | Rat.Le\_Mul.of.LeDiv.Gt\_0 |
| mpr  | Rat.LeDiv.of.Le\_Mul.Gt\_0 |
| mp.comm | Rat.GtMul.of.Gt\_Div.Gt\_0 |
| mpr.comm | Rat.Gt\_Div.of.GtMul.Gt\_0 |
| comm.is | Rat.Gt\_Div.is.GtMul.of.Gt\_0 |
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
