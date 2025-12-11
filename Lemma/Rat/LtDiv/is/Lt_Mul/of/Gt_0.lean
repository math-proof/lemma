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
| main | Rat.LtDiv.is.Lt\_Mul.of.Gt\_0 |
| comm | Rat.Lt\_Mul.is.LtDiv.of.Gt\_0 |
| mp   | Rat.Lt\_Mul.of.LtDiv.Gt\_0 |
| mpr  | Rat.LtDiv.of.Lt\_Mul.Gt\_0 |
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
