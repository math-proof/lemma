import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalMultiOpenBoundaryInfluence
open Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[isingCritical_centeredBox_multiOpen_extremalGap_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalMultiOpenBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_centeredBox_multiOpen_extremalGap_tendsto_zero_eq
  {T : Finset (Site 3)} :
-- imply
  Tendsto (fun n => (gvPlusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real (fmu_multiOpen T) - (gvMinusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real (fmu_multiOpen T)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_centeredBox_multiOpen_extremalGap_tendsto_zero T

/--
[image_add_image_sub_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalMultiOpenBoundaryInfluence.lean)
-/
@[path]
private lemma image_add_image_sub_self_eq
  {x : Site 3}
  {T : Finset (Site 3)} :
-- imply
  (T.image (fun y => x + y)).image (fun y => -x + y) = T := by
-- proof
  apply StatMech.FrontierA.image_add_image_sub_self x T

/--
[gvMeasure_multiOpen_sub_abs_le_critical_centeredGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalMultiOpenBoundaryInfluence.lean)
-/
@[path]
private lemma gvMeasure_multiOpen_sub_abs_le_critical_centeredGap_eq
  {Sout : Finset (Site 3)}
  {eta zeta : ConfigSpace (Site 3)}
  {x : Site 3}
  {r : Nat}
  {T : Finset (Site 3)}
-- given
  (hcontain : (boxFinset 3 r).image (fun y => Multiplicative.ofAdd x • y) ⊆ Sout) :
-- imply
  |(gvMeasure eta Sout (Ising.betaC 3) 0).real (fmu_multiOpen (T.image (fun y => x + y))) - (gvMeasure zeta Sout (Ising.betaC 3) 0).real (fmu_multiOpen (T.image (fun y => x + y)))| ≤ (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real (fmu_multiOpen T) - (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real (fmu_multiOpen T) := by
-- proof
  apply StatMech.FrontierA.gvMeasure_multiOpen_sub_abs_le_critical_centeredGap Sout eta zeta x r T hcontain

/--
[isingCritical_gvBoundary_translatedMultiOpen_sub_abs_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalMultiOpenBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_gvBoundary_translatedMultiOpen_sub_abs_tendsto_zero_eq
  {T : Finset (Site 3)}
-- given
  (Sout : Nat -> Finset (Site 3))
  (eta zeta : Nat -> ConfigSpace (Site 3))
  (x : Nat -> Site 3)
  (radius : Nat -> Nat)
  (hradius : Tendsto radius atTop atTop)
  (hcontain : forall n, (boxFinset 3 (radius n)).image (fun y => Multiplicative.ofAdd (x n) • y) ⊆ Sout n) :
-- imply
  Tendsto (fun n => |(gvMeasure (eta n) (Sout n) (Ising.betaC 3) 0).real (fmu_multiOpen (T.image (fun y => x n + y))) - (gvMeasure (zeta n) (Sout n) (Ising.betaC 3) 0).real (fmu_multiOpen (T.image (fun y => x n + y)))|) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_gvBoundary_translatedMultiOpen_sub_abs_tendsto_zero Sout eta zeta x radius T hradius hcontain


-- created on 2026-10-23
