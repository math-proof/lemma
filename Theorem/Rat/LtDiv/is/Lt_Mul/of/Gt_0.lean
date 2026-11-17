module

public import Theorem.Rat.EqMul_Div.of.Ne_0
public import Theorem.Nat.LtMulS.of.Gt_0.Lt
public import Theorem.Rat.LtDivS.of.Lt.Gt_0
public import Theorem.Nat.EqDivMul.of.Ne_0
public import Theorem.Nat.Ne.of.Gt

public section

open Nat Rat


/--
| attributes | lemma |
| :---: | :---: |
| path | Rat.LtDiv.is.Lt_Mul.of.Gt_0 |
| comm | Rat.Lt_Mul.is.LtDiv.of.Gt_0 |
| mp   | Rat.Lt_Mul.of.LtDiv.Gt_0 |
| mpr  | Rat.LtDiv.of.Lt_Mul.Gt_0 |
| mp.comm | Rat.GtMul.of.Gt_Div.Gt_0 |
| mpr.comm | Rat.Gt_Div.of.GtMul.Gt_0 |
| comm.is | Rat.Gt_Div.is.GtMul.of.Gt_0 |
-/
@[comm, mp, mpr, mp.comm, mpr.comm, comm.is]
public theorem Rat.LtDiv.is.Lt_Mul.of.Gt_0
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
