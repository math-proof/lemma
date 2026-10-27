import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalAxisGreenComparison
open Filter Set Topology StatMech StatMech.FrontierA


/--
[isingTorusNormalizedZeroMode_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalAxisGreenComparison.lean)
-/
@[path]
private lemma isingTorusNormalizedZeroMode_nonneg_eq
  {d : Nat}
  {beta : Real}
  {k : Nat} :
-- imply
  0 <= isingTorusNormalizedZeroMode d beta k := by
-- proof
  apply StatMech.FrontierA.isingTorusNormalizedZeroMode_nonneg beta k

/--
[isingTorusNormalizedZeroMode_tendsto_zero_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalAxisGreenComparison.lean)
-/
@[path]
private lemma isingTorusNormalizedZeroMode_tendsto_zero_subcritical_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hbeta : 0 <= beta)
  (hlt : beta < IsingFK.betaC (magnetization d)) :
-- imply
  Tendsto (isingTorusNormalizedZeroMode d beta) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingTorusNormalizedZeroMode_tendsto_zero_subcritical hd beta hbeta hlt

/--
[isingSiteToDyadicTorus_criticalAxisSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalAxisGreenComparison.lean)
-/
@[path]
private lemma isingSiteToDyadicTorus_criticalAxisSite_eq
  {d : Nat}
  {r k : Nat}
-- given
  (hd : 1 <= d) :
-- imply
  isingSiteToDyadicTorus k (criticalAxisSite hd r) = isingTorusCoordinateShift (k := k) (⟨0, hd⟩ : Fin d) r := by
-- proof
  apply StatMech.FrontierA.isingSiteToDyadicTorus_criticalAxisSite hd r k

/--
[currentContinuityFreeBoxTwoPoint_le_isingTorus_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalAxisGreenComparison.lean)
-/
@[path]
private lemma currentContinuityFreeBoxTwoPoint_le_isingTorus_axis_eq
  {d : Nat}
  {n r k : Nat}
  {beta : Real}
-- given
  (hd : 1 <= d)
  (hr : 1 <= r)
  (hrn : r <= n)
  (hside : 2 * (n + 1) < isingDyadicSide k)
  (hbeta : 0 <= beta) :
-- imply
  currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) (criticalAxisSite hd r) <= isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift (⟨0, hd⟩ : Fin d) r) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeBoxTwoPoint_le_isingTorus_axis hd hr hrn hside beta hbeta

/--
[currentContinuityFreeTwoPoint_axis_le_latticeGreenBlock_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalAxisGreenComparison.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axis_le_latticeGreenBlock_subcritical_eq
  {d : Nat}
  {beta : Real}
  {r : Nat}
-- given
  (hd : 2 < d)
  (hbeta : 0 < beta)
  (hlt : beta < IsingFK.betaC (magnetization d))
  (hr : 1 <= r) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (criticalAxisSite (by omega) r) <= (1 / beta) * isingLatticeGreenAxisBlockAverage (⟨0, by omega⟩ : Fin d) r := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_axis_le_latticeGreenBlock_subcritical hd hbeta hlt r hr

/--
[criticalFreeTwoPoint_axis_le_latticeGreenBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalAxisGreenComparison.lean)
-/
@[path]
private lemma criticalFreeTwoPoint_axis_le_latticeGreenBlock_eq
  {d : Nat}
  {r : Nat}
-- given
  (hd : 2 < d)
  (hr : 1 <= r) :
-- imply
  currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) (criticalAxisSite (by omega) r) <= (1 / IsingFK.betaC (magnetization d)) * isingLatticeGreenAxisBlockAverage (⟨0, by omega⟩ : Fin d) r := by
-- proof
  apply StatMech.FrontierA.criticalFreeTwoPoint_axis_le_latticeGreenBlock hd r hr


-- created on 2026-10-23
