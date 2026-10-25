import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoundaryBridge.Part2
open Filter Topology StatMech StatMech.FrontierA


/--
[rectangularPrismInterfaceDensity_eq_boundaryRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma rectangularPrismInterfaceDensity_eq_boundaryRatio_eq
  {beta : Real}
  {n : Nat} :
-- imply
  rectangularPrismInterfaceDensity beta n = (Real.log (StatMech.Ising.rectangularPrismPlusPartition 1 beta (2 * n + 1) (2 * n + 1) n) - Real.log (StatMech.Ising.rectangularPrismDobrushinPartition 1 beta (2 * n + 1) (2 * n + 1) n)) / ((2 * n + 1 : Nat) : Real) ^ 2 := by
-- proof
  apply StatMech.FrontierA.rectangularPrismInterfaceDensity_eq_boundaryRatio beta n

/--
[oddCubicalIsingDisorderDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma oddCubicalIsingDisorderDensity_tendsto_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (oddCubicalIsingDisorderDensity beta) atTop (nhds (rectangularIsingSurfaceTension beta)) := by
-- proof
  apply StatMech.FrontierA.oddCubicalIsingDisorderDensity_tendsto hbeta

/--
[multibondDisorderFreeEnergy_sheet_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_sheet_sub_abs_le_eq
  [Fintype P]
  [DecidableEq P]
  [Fintype V]
  [DecidableEq V]
  {D D' : Finset P}
-- given
  (ends : P -> V × V)
  (J : P -> Real) :
-- imply
  |multibondDisorderFreeEnergy ends J D - multibondDisorderFreeEnergy ends J D'| <= 2 * ∑ p ∈ D ∆ D', |J p| := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_sheet_sub_abs_le ends J D D'

/--
[rectangularPrismInterfaceDensity_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma rectangularPrismInterfaceDensity_abs_le_eq
  {beta : Real}
  {n : Nat} :
-- imply
  |rectangularPrismInterfaceDensity beta n| <= 2 * |beta| := by
-- proof
  apply StatMech.FrontierA.rectangularPrismInterfaceDensity_abs_le beta n

/--
[oddCubicalIsingDisorderDensity_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma oddCubicalIsingDisorderDensity_abs_le_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  |oddCubicalIsingDisorderDensity beta n| <= 2 * beta := by
-- proof
  apply StatMech.FrontierA.oddCubicalIsingDisorderDensity_abs_le hbeta n

/--
[oddCubical_sub_centralCubical_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma oddCubical_sub_centralCubical_abs_le_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  |oddCubicalIsingDisorderDensity beta n - centralCubicalIsingDisorderDensity beta n| <= 4 * beta := by
-- proof
  apply StatMech.FrontierA.oddCubical_sub_centralCubical_abs_le hbeta n

/--
[prismCubicalDensity_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma prismCubicalDensity_sub_abs_le_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  |rectangularPrismInterfaceDensity beta n - oddCubicalIsingDisorderDensity beta n| <= 4 * beta := by
-- proof
  apply StatMech.FrontierA.prismCubicalDensity_sub_abs_le hbeta n

/--
[standardCubicInterfaceDensity_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_abs_le_eq
  {beta : Real}
  {n : Nat} :
-- imply
  |standardCubicInterfaceDensity beta n| <= 1296 * |beta| := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_abs_le beta n

/--
[standardPrismDensity_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma standardPrismDensity_sub_abs_le_eq
  {beta : Real}
  {n : Nat} :
-- imply
  |standardCubicInterfaceDensity beta n - rectangularPrismInterfaceDensity beta n| <= 1298 * |beta| := by
-- proof
  apply StatMech.FrontierA.standardPrismDensity_sub_abs_le beta n

/--
[rectangularPrismInterfaceDensity_tendsto_of_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma rectangularPrismInterfaceDensity_tendsto_of_comparison_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hcompare : HasPrismCubicalSurfaceComparison beta) :
-- imply
  Tendsto (rectangularPrismInterfaceDensity beta) atTop (nhds (rectangularIsingSurfaceTension beta)) := by
-- proof
  apply StatMech.FrontierA.rectangularPrismInterfaceDensity_tendsto_of_comparison hbeta hcompare

/--
[hasPrismCubicalSurfaceComparison_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma hasPrismCubicalSurfaceComparison_of_tendsto_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hlim : Tendsto (rectangularPrismInterfaceDensity beta) atTop (nhds (rectangularIsingSurfaceTension beta))) :
-- imply
  HasPrismCubicalSurfaceComparison beta := by
-- proof
  apply StatMech.FrontierA.hasPrismCubicalSurfaceComparison_of_tendsto hbeta hlim

/--
[hasPrismCubicalSurfaceComparison_iff_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma hasPrismCubicalSurfaceComparison_iff_tendsto_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  HasPrismCubicalSurfaceComparison beta <-> Tendsto (rectangularPrismInterfaceDensity beta) atTop (nhds (rectangularIsingSurfaceTension beta)) := by
-- proof
  apply StatMech.FrontierA.hasPrismCubicalSurfaceComparison_iff_tendsto hbeta

/--
[standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hprism : HasPrismCubicalSurfaceComparison beta)
  (hstandard : HasStandardPrismSurfaceComparison beta) :
-- imply
  Tendsto (standardCubicInterfaceDensity beta) atTop (nhds (rectangularIsingSurfaceTension beta)) := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension hbeta hprism hstandard

/--
[rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds_eq
  {betaC : Real}
-- given
  (hregime : StatMech.Ising.HasOrderedMagnetizationRegime (StatMech.Ising.magnetization 3) betaC)
  (hzero : 0 <= rectangularIsingSurfaceTension 0)
  (hupper : forall beta, 0 <= beta -> rectangularIsingSurfaceTension beta <= 2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
  (hweak : StatMech.Ising.HasWeakSurfaceTensionLowerBound 1 (StatMech.Ising.magnetization 3) rectangularIsingSurfaceTension) :
-- imply
  forall beta, 0 <= beta -> (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds hregime hzero hupper hweak

/--
[rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds_pos_eq
  {betaC : Real}
-- given
  (hregime : StatMech.Ising.HasOrderedMagnetizationRegime (StatMech.Ising.magnetization 3) betaC)
  (hupper : forall beta, 0 < beta -> rectangularIsingSurfaceTension beta <= 2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
  (hweak : StatMech.Ising.HasWeakSurfaceTensionLowerBound 1 (StatMech.Ising.magnetization 3) rectangularIsingSurfaceTension) :
-- imply
  forall beta, 0 < beta -> (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds_pos hregime hupper hweak

/--
[weakSurfaceTensionLowerBound_of_positive_pointwise_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma weakSurfaceTensionLowerBound_of_positive_pointwise_tendsto_eq
  {J : Real}
-- given
  (M tau : Real -> Real)
  (tauN : Nat -> Real -> Real)
  (hlim : forall beta, 0 < beta -> Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
  (hweak : forall n, StatMech.Ising.HasWeakSurfaceTensionLowerBound J M (tauN n)) :
-- imply
  StatMech.Ising.HasWeakSurfaceTensionLowerBound J M tau := by
-- proof
  apply StatMech.FrontierA.weakSurfaceTensionLowerBound_of_positive_pointwise_tendsto J M tau tauN hlim hweak

/--
[surfaceTensionUpperBound_of_positive_pointwise_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma surfaceTensionUpperBound_of_positive_pointwise_tendsto_eq
  {J : Real}
-- given
  (M tau : Real -> Real)
  (tauN : Nat -> Real -> Real)
  (hlim : forall beta, 0 < beta -> Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
  (hupper : forall n beta, 0 < beta -> tauN n beta <= 2 * J * beta * (M beta) ^ 2) :
-- imply
  forall beta, 0 < beta -> tau beta <= 2 * J * beta * (M beta) ^ 2 := by
-- proof
  apply StatMech.FrontierA.surfaceTensionUpperBound_of_positive_pointwise_tendsto J M tau tauN hlim hupper

/--
[rectangularIsingSurfaceTension_pos_iff_ordered_of_standard_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_iff_ordered_of_standard_bounds_eq
  {betaC : Real}
-- given
  (hregime : StatMech.Ising.HasOrderedMagnetizationRegime (StatMech.Ising.magnetization 3) betaC)
  (hprism : forall beta, 0 < beta -> HasPrismCubicalSurfaceComparison beta)
  (hstandard : forall beta, 0 < beta -> HasStandardPrismSurfaceComparison beta)
  (hupper : forall n beta, 0 < beta -> standardCubicInterfaceDensity beta n <= 2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
  (hweak : forall n, StatMech.Ising.HasWeakSurfaceTensionLowerBound 1 (StatMech.Ising.magnetization 3) (fun beta => standardCubicInterfaceDensity beta n)) :
-- imply
  forall beta, 0 < beta -> (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_iff_ordered_of_standard_bounds hregime hprism hstandard hupper hweak


-- created on 2026-10-23
