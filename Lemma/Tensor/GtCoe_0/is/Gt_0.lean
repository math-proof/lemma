import Lemma.Hyperreal.GtCoe_0.is.Gt_0
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Lt.is.LtDataS
import Lemma.Tensor.Lt0Map.of.Gt_0.All_GtUFn_0
import Lemma.Tensor.MapData.eq.DataMap
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.Lt.is.All_Lt
import sympy.core.relational
open Hyperreal Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GtCoe_0.is.Gt_0 |
| comm | Tensor.Gt_0.is.GtCoe_0 |
| mp | Tensor.Gt_0.of.GtCoe_0 |
| mpr | Tensor.GtCoe_0.of.Gt_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  {X : Tensor ℝ s} :
-- imply
  (X : Tensor ℝ* s) > 0 ↔ X > 0 := by
-- proof
  constructor
  ·
    intro h
    rw [gt_iff_lt, Lt.is.LtDataS, EqData0'0, Lt.is.All_Lt] at h ⊢
    intro i
    have hi := h i
    simp [GetElem.getElem, EqGet0_0.fin] at hi ⊢
    rw [← MapData.eq.DataMap] at hi
    rw [GetMap.eq.UFnGet] at hi
    exact Gt_0.of.GtCoe_0 hi
  ·
    intro h
    apply Lt0Map.of.Gt_0.All_GtUFn_0 _ h
    intro a ha
    exact GtCoe_0.of.Gt_0 ha


-- created on 2026-08-16
