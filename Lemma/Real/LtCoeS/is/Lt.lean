import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.LtCoeS.is.Lt |
| comm | Real.Lt.is.LtCoeS |
| mp   | Real.Lt.of.LtCoeS |
| mpr  | Real.LtCoeS.of.Lt |
| mp.comm | Real.Gt.of.GtCoeS |
| mpr.comm | Real.GtCoeS.of.Gt |
| comm.is | Real.GtCoeS.is.Gt |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
-- given
  (a b : ℝ) :
-- imply
  (a : ℝ*) < (b : ℝ*) ↔ a < b := by
-- proof
  simp


-- created on 2025-12-10
