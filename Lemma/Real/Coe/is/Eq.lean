import sympy.series.limits
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.Coe.is.Eq |
| comm | Real.Eq.is.EqCoeS |
| mp | Real.Eq.of.EqCoeS |
| mpr | Real.EqCoeS.of.Eq |
| mp.mt | Real.NeCoeS.of.Ne |
| mpr.mt | Real.Ne.of.NeCoeS |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  {a b : ℝ} :
-- imply
  (a : ℝ*) = (b : ℝ*) ↔ a = b := by
-- proof
  simp


-- created on 2025-12-10
