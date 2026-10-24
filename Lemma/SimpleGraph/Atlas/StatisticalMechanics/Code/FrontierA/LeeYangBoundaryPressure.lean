import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.LeeYangBoundaryPressure
open Filter Topology StatMech StatMech.FrontierA


/--
[isingBoxPressureSeq_eq_freeBoxFvPressure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoundaryPressure.lean)
-/
@[path]
private lemma isingBoxPressureSeq_eq_freeBoxFvPressure_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  isingBoxPressureSeq d beta h n = Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h) / ((boxFinset d n).card : ℝ) := by
-- proof
  apply StatMech.FrontierA.isingBoxPressureSeq_eq_freeBoxFvPressure d beta h n

/--
[freeBoxFvPressure_tendsto_isingBoxPressureLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoundaryPressure.lean)
-/
@[path]
private lemma freeBoxFvPressure_tendsto_isingBoxPressureLimit_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ) :
-- imply
  Tendsto (fun n => Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h) / ((boxFinset d n).card : ℝ)) atTop (nhds (isingBoxPressureLimit d hd beta h)) := by
-- proof
  apply StatMech.FrontierA.freeBoxFvPressure_tendsto_isingBoxPressureLimit d hd beta h

/--
[minus_free_logFvZ_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoundaryPressure.lean)
-/
@[path]
private lemma minus_free_logFvZ_sub_abs_le_eq
  {d n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  |Real.log (fvZ (minusField d) n (bondFinsetTouch d n) beta h) - Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h)| ≤ |beta| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card := by
-- proof
  apply StatMech.FrontierA.minus_free_logFvZ_sub_abs_le d n beta h

/--
[minus_free_pressure_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoundaryPressure.lean)
-/
@[path]
private lemma minus_free_pressure_indep_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ) :
-- imply
  Tendsto (fun n => Real.log (fvZ (minusField d) n (bondFinsetTouch d n) beta h) / ((boxFinset d n).card : ℝ) - Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h) / ((boxFinset d n).card : ℝ)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.minus_free_pressure_indep d hd beta h

/--
[plusBoxFvPressure_tendsto_isingBoxPressureLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoundaryPressure.lean)
-/
@[path]
private lemma plusBoxFvPressure_tendsto_isingBoxPressureLimit_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ) :
-- imply
  Tendsto (fun n => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) beta h) / ((boxFinset d n).card : ℝ)) atTop (nhds (isingBoxPressureLimit d hd beta h)) := by
-- proof
  apply StatMech.FrontierA.plusBoxFvPressure_tendsto_isingBoxPressureLimit d hd beta h

/--
[minusBoxFvPressure_tendsto_isingBoxPressureLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoundaryPressure.lean)
-/
@[path]
private lemma minusBoxFvPressure_tendsto_isingBoxPressureLimit_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ) :
-- imply
  Tendsto (fun n => Real.log (fvZ (minusField d) n (bondFinsetTouch d n) beta h) / ((boxFinset d n).card : ℝ)) atTop (nhds (isingBoxPressureLimit d hd beta h)) := by
-- proof
  apply StatMech.FrontierA.minusBoxFvPressure_tendsto_isingBoxPressureLimit d hd beta h


-- created on 2026-10-23
