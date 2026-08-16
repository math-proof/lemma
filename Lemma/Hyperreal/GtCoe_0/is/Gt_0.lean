import sympy.series.limits
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.GtCoe_0.is.Gt_0 |
| comm | Hyperreal.Gt_0.is.GtCoe_0 |
| mp | Hyperreal.Gt_0.of.GtCoe_0 |
| mpr | Hyperreal.GtCoe_0.of.Gt_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  {x : ℝ} :
-- imply
  (x : ℝ*) > 0 ↔ x > 0 :=
-- proof
  Hyperreal.coe_pos


-- created on 2026-08-16
