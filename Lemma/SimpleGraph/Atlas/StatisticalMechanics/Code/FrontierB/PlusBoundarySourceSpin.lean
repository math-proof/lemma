import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.PlusBoundarySourceSpin
open MeasureTheory Filter StatMech StatMech.FrontierB


/--
[spinProd_boxSiteSucc_extendInteriorPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoundarySourceSpin.lean)
-/
@[path]
private lemma spinProd_boxSiteSucc_extendInteriorPlus_eq
  {d n : ℕ}
  {tau : ConfigSpace (StatMech.FK.boxVerts d n)}
  {x y : StatMech.FK.boxVerts d n} :
-- imply
  spinProd ({boxSiteSucc x, boxSiteSucc y} : Finset (StatMech.FK.boxVerts d (n + 1))) (extendInteriorPlus (boxCurrentInterior d (n + 1)) ((boxCurrentInteriorConfigEquiv d n).symm tau)) = spinProd ({x.1, y.1} : Finset (Site d)) (glue (plusField d) tau) := by
-- proof
  apply StatMech.FrontierB.spinProd_boxSiteSucc_extendInteriorPlus d n tau x y

/--
[plusPairBoundarySourceRatio_eq_plusIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoundarySourceSpin.lean)
-/
@[path]
private lemma plusPairBoundarySourceRatio_eq_plusIntegral_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n} :
-- imply
  boundarySourceCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y} / boundaryCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (boxCurrentInterior d (n + 1)) = ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.plusPairBoundarySourceRatio_eq_plusIntegral d n beta x y

/--
[growingPlusPairBoundarySourceRatio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoundarySourceSpin.lean)
-/
@[path]
private lemma growingPlusPairBoundarySourceRatio_tendsto_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N) :
-- imply
  Tendsto (fun k => let n := k + N boundarySourceCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (boxCurrentInterior d (n + 1)) {boxSiteSucc (pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)), boxSiteSucc (pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy))} / boundaryCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (boxCurrentInterior d (n + 1))) atTop (nhds (∫ omega, spinProd ({x, y} : Finset (Site d)) omega ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.growingPlusPairBoundarySourceRatio_tendsto d N beta hbeta x y hx hy

/--
[growingFreePairForPlusSwitching_expectation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoundarySourceSpin.lean)
-/
@[path]
private lemma growingFreePairForPlusSwitching_expectation_tendsto_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N) :
-- imply
  Tendsto (fun k => let n := k + N expectationJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) {boxSiteSucc (pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)), boxSiteSucc (pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy))}) atTop (nhds (∫ omega, spinProd ({x, y} : Finset (Site d)) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.growingFreePairForPlusSwitching_expectation_tendsto d N beta hbeta x y hx hy


-- created on 2026-10-23
