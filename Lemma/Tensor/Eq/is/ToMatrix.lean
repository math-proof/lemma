import Lemma.Tensor.Eq.is.All_EqGetS
import sympy.matrices.dense
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Eq.is.ToMatrix |
| comm | Tensor.ToMatrix.is.Eq |
| mp | Tensor.ToMatrix.of.Eq |
| mpr | Tensor.Eq.of.ToMatrix |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (A B : Tensor α [m, n]) :
-- imply
  A = B ↔ A.toMatrix = B.toMatrix := by
-- proof
  constructor
  ·
    intro h
    apply congrArg Tensor.toMatrix h
  ·
    intro h
    apply Tensor.Eq.of.All_EqGetS.fin
    intro i
    apply Tensor.Eq.of.All_EqGetS.fin
    intro j
    apply congrFun (congrFun h i) j


-- created on 2026-09-05
