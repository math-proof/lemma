import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.LtMulS.of.Gt_0.Lt
import Lemma.Nat.Ne.of.Gt
import Lemma.Rat.EqMul_Div.of.Ne_0
import Lemma.Rat.LtDivS.of.Lt.Gt_0
open Rat Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.LtMul.is.Lt\_Div.of.Gt\_0 |
| comm | Rat.Lt\_Div.is.LtMul.of.Gt\_0 |
| mp   | Rat.Lt\_Div.of.LtMul.Gt\_0 |
| mpr  | Rat.LtMul.of.Lt\_Div.Gt\_0 |
| mp.comm | Rat.GtDiv.of.Gt\_Mul.Gt\_0 |
| mpr.comm | Rat.Gt\_Mul.of.GtDiv.Gt\_0 |
| comm.is | Rat.Gt\_Mul.is.GtDiv.of.Gt\_0 |
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
