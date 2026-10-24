import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TailLimit
open MeasureTheory Filter Topology StatMech StatMech.FK


/--
[iInter_crossingEvent_eq_percolationEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TailLimit.lean)
-/
@[path]
private lemma iInter_crossingEvent_eq_percolationEvent_eq
  {d : ℕ} :
-- imply
  (⋂ n : ℕ, crossingEvent d n) = percolationEvent d := by
-- proof
  apply StatMech.FK.iInter_crossingEvent_eq_percolationEvent

/--
[measurableSet_crossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TailLimit.lean)
-/
@[path]
private lemma measurableSet_crossingEvent_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  MeasurableSet (crossingEvent d n) := by
-- proof
  apply StatMech.FK.measurableSet_crossingEvent n

/--
[fkBoundaryConnReal_tendsto_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TailLimit.lean)
-/
@[path]
private lemma fkBoundaryConnReal_tendsto_fkTheta_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  Tendsto (fun n => fkBoundaryConnReal d hp hp1 hq n) atTop (𝓝 (fkTheta d hp hp1 hq (q := q))) := by
-- proof
  apply StatMech.FK.fkBoundaryConnReal_tendsto_fkTheta hp hp1 hq

/--
[fkTheta_eq_lim_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TailLimit.lean)
-/
@[path]
private lemma fkTheta_eq_lim_boundary_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkTheta d hp hp1 hq (q := q) = limUnder atTop (fun n => fkBoundaryConnReal d hp hp1 hq n) := by
-- proof
  apply StatMech.FK.fkTheta_eq_lim_boundary hp hp1 hq


-- created on 2026-10-23
