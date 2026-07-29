import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.LtMulS.of.Gt_0.Lt
import Lemma.Nat.Ne.of.Gt
import Lemma.Rat.EqMul_Div.of.Ne_0
import Lemma.Rat.LtDivS.of.Lt.Gt_0
open Rat Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.LtMul.is.Lt_Div.of.Gt_0 |
| comm | Rat.Lt_Div.is.LtMul.of.Gt_0 |
| mp   | Rat.Lt_Div.of.LtMul.Gt_0 |
| mpr  | Rat.LtMul.of.Lt_Div.Gt_0 |
| mp.comm | Rat.GtDiv.of.Gt_Mul.Gt_0 |
| mpr.comm | Rat.Gt_Mul.of.GtDiv.Gt_0 |
| comm.is | Rat.Gt_Mul.is.GtDiv.of.Gt_0 |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x > 0)
  (y k : α) :
-- imply
  x * k < y ↔ k < y / x := by
-- proof
  constructor <;>
    intro h_lt
  ·
    have := LtDivS.of.Lt.Gt_0 h_lt h
    rwa [EqDivMul.of.Ne_0.left] at this
    apply Ne.of.Gt h
  ·
    have := LtMulS.of.Gt_0.Lt h h_lt
    rwa [EqMul_Div.of.Ne_0] at this
    apply Ne.of.Gt h


-- created on 2025-12-11
