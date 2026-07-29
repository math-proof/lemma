import Lemma.Rat.EqMul_Div.of.Ne_0
import Lemma.Nat.LtMulS.of.Gt_0.Lt
import Lemma.Rat.EqMulDiv.of.Ne_0
import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Ne.of.Gt
open Nat Rat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.LtDiv.is.Lt_Mul.of.Gt_0 |
| comm | Rat.Lt_Mul.is.LtDiv.of.Gt_0 |
| mp   | Rat.Lt_Mul.of.LtDiv.Gt_0 |
| mpr  | Rat.LtDiv.of.Lt_Mul.Gt_0 |
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
  (y k : α):
-- imply
  y / x < k ↔ y < x * k := by
-- proof
  constructor <;>
    intro h_lt
  .
    have := LtMulS.of.Gt_0.Lt h h_lt
    rwa [EqMul_Div.of.Ne_0] at this
    apply Ne.of.Gt h
  .
    have := LtDivS.of.Lt.Gt_0 h_lt h
    rwa [EqDivMul.of.Ne_0.left] at this
    apply Ne.of.Gt h


-- created on 2025-07-06
