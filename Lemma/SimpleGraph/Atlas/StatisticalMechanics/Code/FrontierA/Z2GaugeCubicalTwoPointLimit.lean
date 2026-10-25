import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalTwoPointLimit
open MeasureTheory Filter Topology StatMech StatMech.FrontierA


/--
[oddPrismPlusTwoPoint_eq_plusMeasure_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointLimit.lean)
-/
@[path]
private lemma oddPrismPlusTwoPoint_eq_plusMeasure_pair_eq
  {beta : Real}
  {n : Nat}
  {v w : RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  oddPrismPlusTwoPoint 1 beta n v w = ∫ omega, spin omega (rectangularPrismSiteEquivSctBoxDobrushin n v).1 * spin omega (rectangularPrismSiteEquivSctBoxDobrushin n w).1 ∂(plusMeasure 3 n beta 0 : Measure (ConfigSpace (Site 3))) := by
-- proof
  apply StatMech.FrontierA.oddPrismPlusTwoPoint_eq_plusMeasure_pair beta n v w

/--
[oddCubicalDualTwoPoint_eq_plusMeasure_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointLimit.lean)
-/
@[path]
private lemma oddCubicalDualTwoPoint_eq_plusMeasure_pair_eq
  {beta : Real}
  {n : Nat}
  {q r : CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1)} :
-- imply
  multibondIsingTwoPoint cubicalDualEnds (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta) (some q) (some r) = ∫ omega, spin omega (rectangularPrismSiteEquivSctBoxDobrushin n (oddCubicalCellEquivPrismSite n q)).1 * spin omega (rectangularPrismSiteEquivSctBoxDobrushin n (oddCubicalCellEquivPrismSite n r)).1 ∂(plusMeasure 3 n beta 0 : Measure (ConfigSpace (Site 3))) := by
-- proof
  apply StatMech.FrontierA.oddCubicalDualTwoPoint_eq_plusMeasure_pair beta n q r

/--
[tendsto_finset_prod_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointLimit.lean)
-/
@[path]
private lemma tendsto_finset_prod_one_sub_eq
  {s : Finset I}
-- given
  (corr : Nat -> I -> Real)
  (limitCorr : I -> Real)
  (hcorr : forall i, i ∈ s -> Tendsto (fun n => corr n i) atTop (nhds (limitCorr i))) :
-- imply
  Tendsto (fun n => ∏ i ∈ s, (1 - corr n i)) atTop (nhds (∏ i ∈ s, (1 - limitCorr i))) := by
-- proof
  apply StatMech.FrontierA.tendsto_finset_prod_one_sub s corr limitCorr hcorr

/--
[finiteCylinderProduct_le_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointLimit.lean)
-/
@[path]
private lemma finiteCylinderProduct_le_of_tendsto_eq
  {s : Finset I}
  {limitWilson : Real}
-- given
  (corr : Nat -> I -> Real)
  (limitCorr : I -> Real)
  (wilson : Nat -> Real)
  (hcorr : forall i, i ∈ s -> Tendsto (fun n => corr n i) atTop (nhds (limitCorr i)))
  (hwilson : Tendsto wilson atTop (nhds limitWilson))
  (hfinite : forall n, (∏ i ∈ s, (1 - corr n i)) <= wilson n) :
-- imply
  (∏ i ∈ s, (1 - limitCorr i)) <= limitWilson := by
-- proof
  apply StatMech.FrontierA.finiteCylinderProduct_le_of_tendsto s corr limitCorr wilson limitWilson hcorr hwilson hfinite


-- created on 2026-10-23
