import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityAxisInfrared
open Filter Finset MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[currentContinuityFreeBoxTwoPoint_le_isingTorusAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeBoxTwoPoint_le_isingTorusAxis_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {n r k : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (hrpos : 0 < r)
  (hrn : r ≤ n)
  (hside : 2 * (n + 1) < isingDyadicSide k) :
-- imply
  currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) (Pi.single i (-(r : Int))) ≤ isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeBoxTwoPoint_le_isingTorusAxis i beta hbeta n r k hrpos hrn hside

/--
[currentContinuityFreeTwoPoint_axis_le_of_eventually_torus_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axis_le_of_eventually_torus_le_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {r : Nat}
  {bound : Real}
-- given
  (hbeta : 0 ≤ beta)
  (hr : 0 < r)
  (hbound : ∀ᶠ k : Nat in atTop, isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) ≤ bound) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (-(r : Int))) ≤ bound := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeTwoPoint_axis_le_of_eventually_torus_le i beta hbeta r hr bound hbound

/--
[currentContinuityFreeTwoPoint_axis_le_sparseGreenBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axis_le_sparseGreenBound_eq
  {d : Nat}
  {beta : Real}
  {delta : Real}
  {M : Real}
  {R : Nat}
  {i : Fin d}
  {count r : Nat}
-- given
  (hd : 2 < d)
  (hbeta : 0 < beta)
  (hlt : beta < IsingFK.betaC (StatMech.Ising.magnetization d))
  (hdelta : 0 < delta)
  (hgreen : ∀ (i : Fin d) (spacing count : Nat), R < spacing → 0 < count → ∀ᶠ k : Nat in atTop, finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k))) (isingTorusSparseAxisBlock i spacing count) ≤ M / count + delta)
  (hcount : 2 ≤ count)
  (hrlarge : (R + 1) * (count - 1) ≤ r) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (-(r : Int))) ≤ delta + (1 / beta) * (M / count + delta) := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeTwoPoint_axis_le_sparseGreenBound hd beta hbeta hlt delta hdelta M R hgreen i count r hcount hrlarge

/--
[currentContinuityAxisSite_eq_negative_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisInfrared.lean)
-/
@[path]
private lemma currentContinuityAxisSite_eq_negative_single_eq
  {d : Nat}
  {r : Nat}
-- given
  (hd : 1 ≤ d) :
-- imply
  currentContinuityAxisSite hd r = Pi.single (⟨0, hd⟩ : Fin d) (-(r : Int)) := by
-- proof
  apply StatMech.FrontierB.currentContinuityAxisSite_eq_negative_single hd r

/--
[currentContinuityFreeTwoPoint_negativeAxis_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_negativeAxis_nonneg_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {r : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (hr : 0 < r) :
-- imply
  0 ≤ currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (-(r : Int))) := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeTwoPoint_negativeAxis_nonneg i beta hbeta r hr

/--
[currentContinuityFreeAxisLROZero_at_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeAxisLROZero_at_betaC_eq
  {d : Nat}
-- given
  (hd : 2 < d)
  (hbetaC : 0 < IsingFK.betaC (StatMech.Ising.magnetization d)) :
-- imply
  CurrentContinuityFreeAxisLROZero d (by omega) (IsingFK.betaC (StatMech.Ising.magnetization d)) := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeAxisLROZero_at_betaC hd hbetaC

/--
[currentContinuityFreeAxisLROZero_at_isingCritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisInfrared.lean)
-/
@[path]
private lemma currentContinuityFreeAxisLROZero_at_isingCritical_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  CurrentContinuityFreeAxisLROZero d (by omega) (IsingFK.betaC (StatMech.Ising.magnetization d)) := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeAxisLROZero_at_isingCritical hd


-- created on 2026-10-23
