import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper.Part3
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectCutMedialColumn_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectCutMedialColumn_val_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {b : Bool} :
-- imply
  (fkRectCutMedialColumn R x b).val = b.toNat + 2 * x.val := by
-- proof
  apply StatMech.FrontierD.fkRectCutMedialColumn_val R x b

/--
[fkRectCutMedialColumn_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectCutMedialColumn_snd_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {b : Bool} :
-- imply
  (fkRectMedialVertexOfEdge R (b, (x, ⟨0, R.height_pos⟩))).2 = ⟨0, R.height_pos⟩ := by
-- proof
  apply StatMech.FrontierD.fkRectCutMedialColumn_snd R x b

/--
[fkRectCutMedialColumn_false_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectCutMedialColumn_false_succ_eq
  {R : FKRectTorus}
  {x : Fin R.width} :
-- imply
  finitePeriodicSucc R.medialTorus.width_pos (fkRectCutMedialColumn R x false) = fkRectCutMedialColumn R x true := by
-- proof
  apply StatMech.FrontierD.fkRectCutMedialColumn_false_succ R x

/--
[fkRectTorusMedialEdgeEquiv_cutColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectTorusMedialEdgeEquiv_cutColumn_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {b : Bool} :
-- imply
  fkRectTorusMedialEdgeEquiv R (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩) = (b, (x, ⟨0, R.height_pos⟩)) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusMedialEdgeEquiv_cutColumn R x b

/--
[fkRectCutMedialColumn_canonicalVerticalSeamSign_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectCutMedialColumn_canonicalVerticalSeamSign_add_eq
  {R : FKRectTorus}
  {x : Fin R.width} :
-- imply
  fkMedialCanonicalVerticalSeamSign R.medialTorus (fkRectCutMedialColumn R x false) + fkMedialCanonicalVerticalSeamSign R.medialTorus (fkRectCutMedialColumn R x true) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectCutMedialColumn_canonicalVerticalSeamSign_add R x

/--
[fkRectCutMedialColumns_reachable_of_both_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectCutMedialColumns_reachable_of_both_open_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : Fin R.width}
-- given
  (hfalse : omega (false, (x, ⟨0, R.height_pos⟩)) = true)
  (htrue : omega (true, (x, ⟨0, R.height_pos⟩)) = true) :
-- imply
  (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).Reachable (fkMedialVerticalSeamDart R.medialTorus (fkRectCutMedialColumn R x false)) (fkMedialVerticalSeamDart R.medialTorus (fkRectCutMedialColumn R x true)) := by
-- proof
  apply StatMech.FrontierD.fkRectCutMedialColumns_reachable_of_both_open R omega x hfalse htrue

/--
[fkRectCutMedialColumns_component_eq_of_both_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectCutMedialColumns_component_eq_of_both_open_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : Fin R.width}
-- given
  (hfalse : omega (false, (x, ⟨0, R.height_pos⟩)) = true)
  (htrue : omega (true, (x, ⟨0, R.height_pos⟩)) = true) :
-- imply
  (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkMedialVerticalSeamDart R.medialTorus (fkRectCutMedialColumn R x false)) = (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkMedialVerticalSeamDart R.medialTorus (fkRectCutMedialColumn R x true)) := by
-- proof
  apply StatMech.FrontierD.fkRectCutMedialColumns_component_eq_of_both_open R omega x hfalse htrue

/--
[fkMedialLoopCanonicalVerticalFlux_eq_sum_cutColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkMedialLoopCanonicalVerticalFlux_eq_sum_cutColumns_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)} :
-- imply
  fkMedialLoopCanonicalVerticalFlux (fkRectConfigurationToMedialPairing R omega) C = ∑ x : Fin R.width, (fkRectMedialLoopCutColumnContribution R omega C x false + fkRectMedialLoopCutColumnContribution R omega C x true) := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCanonicalVerticalFlux_eq_sum_cutColumns R omega C

/--
[fkRectAllButOneOpenSeamEvent_both_open_of_column_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectAllButOneOpenSeamEvent_both_open_of_column_ne_eq
  {R : FKRectTorus}
  {gap : R.EdgeIndex}
  {omega : R.Configuration}
  {x : Fin R.width}
-- given
  (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
  (hx : x ≠ gap.2.1) :
-- imply
  omega (false, (x, ⟨0, R.height_pos⟩)) = true ∧ omega (true, (x, ⟨0, R.height_pos⟩)) = true := by
-- proof
  apply StatMech.FrontierD.fkRectAllButOneOpenSeamEvent_both_open_of_column_ne R homega hx

/--
[fkRectMedialLoopCutColumnContribution_add_eq_zero_of_ne_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectMedialLoopCutColumnContribution_add_eq_zero_of_ne_gap_eq
  {R : FKRectTorus}
  {gap : R.EdgeIndex}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)}
  {x : Fin R.width}
-- given
  (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
  (hx : x ≠ gap.2.1) :
-- imply
  fkRectMedialLoopCutColumnContribution R omega C x false + fkRectMedialLoopCutColumnContribution R omega C x true = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCutColumnContribution_add_eq_zero_of_ne_gap R homega C hx

/--
[fkMedialLoopCanonicalVerticalFlux_eq_gapColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkMedialLoopCanonicalVerticalFlux_eq_gapColumn_eq
  {R : FKRectTorus}
  {gap : R.EdgeIndex}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)}
-- given
  (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
-- imply
  fkMedialLoopCanonicalVerticalFlux (fkRectConfigurationToMedialPairing R omega) C = fkRectMedialLoopCutColumnContribution R omega C gap.2.1 false + fkRectMedialLoopCutColumnContribution R omega C gap.2.1 true := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCanonicalVerticalFlux_eq_gapColumn R homega C

/--
[sum_natAbs_fkRectMedialLoopCutColumnContribution_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma sum_natAbs_fkRectMedialLoopCutColumnContribution_eq_one_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : Fin R.width}
  {b : Bool} :
-- imply
  ∑ C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega), (fkRectMedialLoopCutColumnContribution R omega C x b).natAbs = 1 := by
-- proof
  apply StatMech.FrontierD.sum_natAbs_fkRectMedialLoopCutColumnContribution_eq_one R omega x b

/--
[fkMedialUnorientedVerticalWindingTotal_le_two_of_allButOneOpenSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkMedialUnorientedVerticalWindingTotal_le_two_of_allButOneOpenSeam_eq
  {R : FKRectTorus}
  {gap : R.EdgeIndex}
  {omega : R.Configuration}
-- given
  (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
-- imply
  fkMedialUnorientedVerticalWindingTotal (fkRectConfigurationToMedialPairing R omega) ≤ 2 := by
-- proof
  apply StatMech.FrontierD.fkMedialUnorientedVerticalWindingTotal_le_two_of_allButOneOpenSeam R homega

/--
[fkRectUnorientedVerticalWindingNumber_le_one_of_allButOneOpenSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_le_one_of_allButOneOpenSeam_eq
  {R : FKRectTorus}
  {gap : R.EdgeIndex}
  {omega : R.Configuration}
-- given
  (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
-- imply
  fkRectUnorientedVerticalWindingNumber R omega ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_le_one_of_allButOneOpenSeam R homega

/--
[fkRectAugmentedSourceBarrier_subset_allButOneOpenSeamEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectAugmentedSourceBarrier_subset_allButOneOpenSeamEvent_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width} :
-- imply
  fkRectAugmentedSourceBarrier R leftRight gap x ⊆ fkRectAllButOneOpenSeamEvent R gap := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSourceBarrier_subset_allButOneOpenSeamEvent R leftRight gap x

/--
[fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hleft : leftRight + 1 < R.width)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut ≤ x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  fkRectAugmentedBarrierConnectionEvent R leftRight cut gap x t ⊆ fkRectFullGraphEvent R {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne R leftRight cut hleft hgap x hx hchosen t hpair

/--
[fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 ≤ q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut ≤ x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectAugmentedSourceBarrier R leftRight gap x) ≤ fkRectCriticalEventMass R q {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass R leftRight cut hsep hleft hq hgap x hx hchosen t hpair

/--
[fkRectSource_barrierConnectionProduct_le_windingOneMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean)
-/
@[path]
private lemma fkRectSource_barrierConnectionProduct_le_windingOneMass_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 ≤ q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut ≤ x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  FK.cFE (fkRectCriticalP q) q * (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap) ≤ fkRectCriticalEventMass R q {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
-- proof
  apply StatMech.FrontierD.fkRectSource_barrierConnectionProduct_le_windingOneMass R leftRight cut hsep hleft hq hgap x hx hchosen t hpair


-- created on 2026-10-23
