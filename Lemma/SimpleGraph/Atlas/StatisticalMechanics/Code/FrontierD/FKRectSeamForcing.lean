import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
open Finset StatMech StatMech.FrontierD


/--
[fkRectHorizontalCutEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectHorizontalCutEdges_card_eq
  {R : FKRectTorus} :
-- imply
  (fkRectHorizontalCutEdges R).card = 2 * R.width := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCutEdges_card R

/--
[fkRectVerticalCutEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectVerticalCutEdges_card_eq
  {R : FKRectTorus} :
-- imply
  (fkRectVerticalCutEdges R).card = R.height := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalCutEdges_card R

/--
[fkRectTorusCutEdges_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectTorusCutEdges_card_le_eq
  {R : FKRectTorus} :
-- imply
  (fkRectTorusCutEdges R).card ≤ 2 * R.width + R.height := by
-- proof
  apply StatMech.FrontierD.fkRectTorusCutEdges_card_le R

/--
[fkRectCritical_cFE_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCritical_cFE_nonneg_eq
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  0 ≤ StatMech.FK.cFE (fkRectCriticalP q) q := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_nonneg hq

/--
[fkRectCritical_cFE_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCritical_cFE_le_one_eq
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  StatMech.FK.cFE (fkRectCriticalP q) q ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_le_one hq

/--
[fkRectCritical_cutClosedMass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCritical_cutClosedMass_lower_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  StatMech.FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) ≤ fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cutClosedMass_lower R hq

/--
[fkRectForceCutClosed_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectForceCutClosed_of_mem_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∈ fkRectTorusCutEdges R) :
-- imply
  fkRectForceCutClosed R omega a = false := by
-- proof
  apply StatMech.FrontierD.fkRectForceCutClosed_of_mem R omega a ha

/--
[fkRectForceCutClosed_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectForceCutClosed_of_not_mem_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∉ fkRectTorusCutEdges R) :
-- imply
  fkRectForceCutClosed R omega a = omega a := by
-- proof
  apply StatMech.FrontierD.fkRectForceCutClosed_of_not_mem R omega a ha

/--
[fkRectForceCutClosed_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectForceCutClosed_idem_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectForceCutClosed R (fkRectForceCutClosed R omega) = fkRectForceCutClosed R omega := by
-- proof
  apply StatMech.FrontierD.fkRectForceCutClosed_idem R omega

/--
[fkRectCutClosedConfiguration_forceCutClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCutClosedConfiguration_forceCutClosed_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  FKRectCutClosedConfiguration R (fkRectForceCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectCutClosedConfiguration_forceCutClosed R omega

/--
[fkRectCutClosedConfiguration_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCutClosedConfiguration_iff_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  FKRectCutClosedConfiguration R eta ↔ ∀ a ∈ fkRectTorusCutEdges R, eta a = false := by
-- proof
  apply StatMech.FrontierD.fkRectCutClosedConfiguration_iff R eta

/--
[fkRectCutHorizontalCrossingSourceCount_le_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCutHorizontalCrossingSourceCount_le_height_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectCutHorizontalCrossingSourceCount R omega ≤ R.height := by
-- proof
  apply StatMech.FrontierD.fkRectCutHorizontalCrossingSourceCount_le_height R omega

/--
[fkRectCutHorizontalCrossingClusterCount_le_sourceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCutHorizontalCrossingClusterCount_le_sourceCount_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectCutHorizontalCrossingClusterCount R omega ≤ fkRectCutHorizontalCrossingSourceCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectCutHorizontalCrossingClusterCount_le_sourceCount R omega

/--
[fkRectCriticalCutHorizontalCrossingSourceExpectation_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCriticalCutHorizontalCrossingSourceExpectation_eq_sum_eq
  {R : FKRectTorus}
  {q : Real} :
-- imply
  fkRectCriticalCutHorizontalCrossingSourceExpectation R q = ∑ y : Fin R.height, fkRectCriticalCutHorizontalCrossingSourceMass R q y := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutHorizontalCrossingSourceExpectation_eq_sum R q

/--
[fkRectCriticalCutHorizontalCrossingSourceExpectation_le_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCriticalCutHorizontalCrossingSourceExpectation_le_height_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalCutHorizontalCrossingSourceExpectation R q ≤ R.height := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutHorizontalCrossingSourceExpectation_le_height R hq

/--
[fkRectCriticalCutHorizontalCrossingClusterExpectation_le_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCriticalCutHorizontalCrossingClusterExpectation_le_source_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalCutHorizontalCrossingClusterExpectation R q ≤ fkRectCriticalCutHorizontalCrossingSourceExpectation R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutHorizontalCrossingClusterExpectation_le_source R hq

/--
[fkRectCriticalZeroTurnExpectation_le_two_width_add_cutCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCriticalZeroTurnExpectation_le_two_width_add_cutCrossing_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q)
  (hcut : ∀ omega : R.Configuration, fkRectZeroTurnLoopCount R omega ≤ 2 * R.width + fkRectCutHorizontalCrossingSourceCount R omega) :
-- imply
  fkRectCriticalZeroTurnExpectation R q ≤ 2 * R.width + fkRectCriticalCutHorizontalCrossingSourceExpectation R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalZeroTurnExpectation_le_two_width_add_cutCrossing R hq hcut

/--
[fkRectCriticalZeroTurnExpectation_le_two_width_add_cutClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean)
-/
@[path]
private lemma fkRectCriticalZeroTurnExpectation_le_two_width_add_cutClusters_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q)
  (hcut : ∀ omega : R.Configuration, fkRectZeroTurnLoopCount R omega ≤ 2 * R.width + fkRectCutHorizontalCrossingClusterCount R omega) :
-- imply
  fkRectCriticalZeroTurnExpectation R q ≤ 2 * R.width + fkRectCriticalCutHorizontalCrossingClusterExpectation R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalZeroTurnExpectation_le_two_width_add_cutClusters R hq hcut


-- created on 2026-10-23
