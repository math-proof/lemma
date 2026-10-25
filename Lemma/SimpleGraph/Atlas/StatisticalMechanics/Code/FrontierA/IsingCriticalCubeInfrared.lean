import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalCubeInfrared
open Filter Finset MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[isingSiteToDyadicTorus_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma isingSiteToDyadicTorus_sub_eq
  {d : Nat}
  {k : Nat}
  {a b : Site d} :
-- imply
  isingSiteToDyadicTorus k (b - a) = isingSiteToDyadicTorus k b - isingSiteToDyadicTorus k a := by
-- proof
  apply StatMech.FrontierA.isingSiteToDyadicTorus_sub k a b

/--
[currentContinuityFreeBoxPositiveCubeAverage_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeBoxPositiveCubeAverage_tendsto_eq
  {d : Nat}
  {beta : Real}
  {m : Nat}
-- given
  (hbeta : 0 <= beta) :
-- imply
  Tendsto (fun n => currentContinuityFreeBoxPositiveCubeAverage d n beta m) atTop (nhds (currentContinuityFreePositiveCubeAverage d beta m)) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeBoxPositiveCubeAverage_tendsto beta hbeta m

/--
[currentContinuityFreeTwoPoint_axis_le_pairKernel_of_l1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axis_le_pairKernel_of_l1_eq
  {d : Nat}
  {j : Fin d}
  {beta : Real}
  {r : Nat}
  {z : Site d}
-- given
  (hd : 2 <= d)
  (hbeta : 0 < beta)
  (hr : 1 <= r)
  (hz : (∑ i, (z i).natAbs) <= r) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single j (r : Int)) <= currentContinuityFreePairKernel d beta z := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_axis_le_pairKernel_of_l1 hd j beta hbeta r hr z hz

/--
[currentContinuityFreeTwoPoint_axis_le_positiveCube_pairKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axis_le_positiveCube_pairKernel_eq
  {d : Nat}
  {j : Fin d}
  {beta : Real}
  {r m : Nat}
  {a b : Site d}
-- given
  (hd : 2 <= d)
  (hbeta : 0 < beta)
  (hr : 1 <= r)
  (hdm : d * m <= r)
  (ha : a ∈ isingPositiveCube d m)
  (hb : b ∈ isingPositiveCube d m) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single j (r : Int)) <= currentContinuityFreePairKernel d beta (b - a) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_axis_le_positiveCube_pairKernel hd j beta hbeta r m hr hdm ha hb

/--
[currentContinuityFreeBoxPairKernel_le_isingTorus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeBoxPairKernel_le_isingTorus_eq
  {d : Nat}
  {beta : Real}
  {n k : Nat}
  {z : Site d}
-- given
  (hbeta : 0 <= beta)
  (hside : 2 * (n + 1) < isingDyadicSide k)
  (hzBox : z ∈ box d n) :
-- imply
  currentContinuityFreeBoxPairKernel d n beta z <= isingTorusTwoPoint (k := k) beta 0 (isingSiteToDyadicTorus k z) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeBoxPairKernel_le_isingTorus beta hbeta n k hside z hzBox

/--
[currentContinuityFreeBoxPositiveCubeAverage_le_isingTorus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeBoxPositiveCubeAverage_le_isingTorus_eq
  {d : Nat}
  {beta : Real}
  {m n k : Nat}
-- given
  (hbeta : 0 <= beta)
  (hmn : m <= n)
  (hside : 2 * (n + 1) < isingDyadicSide k) :
-- imply
  currentContinuityFreeBoxPositiveCubeAverage d n beta m <= finiteTorusBlockDifferenceAverage (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) (isingTorusPositiveCube d m k) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeBoxPositiveCubeAverage_le_isingTorus beta hbeta m n k hmn hside

/--
[exists_currentContinuityFreePositiveCubeAverage_le_power_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma exists_currentContinuityFreePositiveCubeAverage_le_power_subcritical_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ (beta : Real), 0 < beta -> beta < IsingFK.betaC (magnetization d) -> ∀ m : Nat, 2 <= m -> currentContinuityFreePositiveCubeAverage d beta m <= (1 / beta) * (C / (m : Real) ^ (d - 2)) := by
-- proof
  apply StatMech.FrontierA.exists_currentContinuityFreePositiveCubeAverage_le_power_subcritical hd

/--
[currentContinuityFreeTwoPoint_axis_le_positiveCubeAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axis_le_positiveCubeAverage_eq
  {d : Nat}
  {j : Fin d}
  {beta : Real}
  {r m : Nat}
-- given
  (hd : 2 <= d)
  (hbeta : 0 < beta)
  (hr : 1 <= r)
  (hm : 1 <= m)
  (hdm : d * m <= r) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single j (r : Int)) <= currentContinuityFreePositiveCubeAverage d beta m := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_axis_le_positiveCubeAverage hd j beta hbeta r m hr hm hdm

/--
[exists_currentContinuityFreeTwoPoint_axis_le_power_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma exists_currentContinuityFreeTwoPoint_axis_le_power_subcritical_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ (beta : Real), 0 < beta -> beta < IsingFK.betaC (magnetization d) -> ∀ (j : Fin d) (r : Nat), 2 * d <= r -> currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single j (r : Int)) <= (1 / beta) * (C / (r : Real) ^ (d - 2)) := by
-- proof
  apply StatMech.FrontierA.exists_currentContinuityFreeTwoPoint_axis_le_power_subcritical hd

/--
[exists_criticalFreeTwoPoint_axis_le_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma exists_criticalFreeTwoPoint_axis_le_power_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ (j : Fin d) (r : Nat), 2 * d <= r -> currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) (Pi.single j (r : Int)) <= C / (r : Real) ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.exists_criticalFreeTwoPoint_axis_le_power hd

/--
[exists_criticalFreeTwoPoint_shell_le_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma exists_criticalFreeTwoPoint_shell_le_power_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ (r : Nat), 2 * d <= r -> ∀ x ∈ boxSV_vbF d r, currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <= C / (r : Real) ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.exists_criticalFreeTwoPoint_shell_le_power hd

/--
[criticalFreeTwoPoint_shell_powerBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean)
-/
@[path]
private lemma criticalFreeTwoPoint_shell_powerBounds_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ (r : Nat), 2 * d <= r -> ∀ x ∈ boxSV_vbF d r, 1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) * (2 * ((d * r : Nat) : Real) + 1) ^ (d - 1)) <= currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x ∧ currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <= C / (r : Real) ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.criticalFreeTwoPoint_shell_powerBounds hd


-- created on 2026-10-23
