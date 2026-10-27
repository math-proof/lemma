import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectRefinedBoundaryCenterAfter_dualShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryCenterAfter_dualShift_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {n : Nat} :
-- imply
  fkRectRefinedBoundaryCenterAfter (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega)) (fkRectMedialDualShiftDart R d) c n = fkRectRefinedBoundaryCenterAfter (fkRectConfigurationToMedialPairing R omega) d c n := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryCenterAfter_dualShift R omega d c n

/--
[fkRectMedialBoundaryPrimalSeamTrace_dualShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalSeamTrace_dualShift_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
-- given
  (hclosed : (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[n] d = d) :
-- imply
  fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega)) (fkRectMedialDualShiftDart R d) n = fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R omega) d n := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalSeamTrace_dualShift R omega d n hclosed

/--
[fkRectZeroTurnRemainderDualBoundaryCycleWalk_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderDualBoundaryCycleWalk_winding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  fkRectWalkWinding R (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C) = fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C)) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderDualBoundaryCycleWalk_winding R omega C

/--
[mem_fkRectZeroTurnPrimalTouchedCrossings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma mem_fkRectZeroTurnPrimalTouchedCrossings_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C ↔ ∃ x ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C)).support, (fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk x = X.1 := by
-- proof
  apply StatMech.FrontierD.mem_fkRectZeroTurnPrimalTouchedCrossings R omega C X

/--
[fkRectZeroTurnPrimalTouchedCrossing_matches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnPrimalTouchedCrossing_matches_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C) :
-- imply
  FKRectZeroTurnCrossingMatches R omega C X := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnPrimalTouchedCrossing_matches R omega C X hX

/--
[fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hXC : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
  (hXD : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega D) :
-- imply
  fkRectZeroTurnRemainderPrimalComponent R omega C = fkRectZeroTurnRemainderPrimalComponent R omega D := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing R omega C D X hXC hXD

/--
[fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (havoid : FKRectWalkAvoidsRowSeam R (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C))) :
-- imply
  (fkRectZeroTurnPrimalTouchedCrossings R omega C).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam R omega C havoid

/--
[mem_fkRectZeroTurnDualTouchedCrossings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma mem_fkRectZeroTurnDualTouchedCrossings_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawWiredDualHorizontalCrossingComponent R omega} :
-- imply
  X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ↔ ∃ x ∈ (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).support, (fkRectOpenGraph R (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega))).connectedComponentMk x = X.1 := by
-- proof
  apply StatMech.FrontierD.mem_fkRectZeroTurnDualTouchedCrossings R omega C X

/--
[fkRectOpenGraph_dual_le_dual_forceCutClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectOpenGraph_dual_le_dual_forceCutClosed_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega) ≤ fkRectOpenGraph R (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega)) := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_dual_le_dual_forceCutClosed R omega

/--
[fkRectZeroTurnDualTouchedCrossings_nonempty_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnDualTouchedCrossings_nonempty_of_winding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hwind : (fkRectWalkWinding R (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C)).1 ≠ 0) :
-- imply
  (fkRectZeroTurnDualTouchedCrossings R omega C).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnDualTouchedCrossings_nonempty_of_winding R omega C hwind

/--
[fkRectZeroTurnDualTouchedCrossings_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnDualTouchedCrossings_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  (fkRectZeroTurnDualTouchedCrossings R omega C).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnDualTouchedCrossings_nonempty R omega C

/--
[fkRectZeroTurnMixedTouchedCrossings_eq_primal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnMixedTouchedCrossings_eq_primal_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
-- imply
  fkRectZeroTurnMixedTouchedCrossings R omega C = fkRectZeroTurnPrimalTouchedCrossingsInMixed R omega C := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnMixedTouchedCrossings_eq_primal R omega C hC

/--
[fkRectZeroTurnMixedTouchedCrossings_eq_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnMixedTouchedCrossings_eq_dual_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
-- imply
  fkRectZeroTurnMixedTouchedCrossings R omega C = fkRectZeroTurnDualTouchedCrossingsInMixed R omega C := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnMixedTouchedCrossings_eq_dual R omega C hC

/--
[mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  Sum.inl X ∈ fkRectZeroTurnMixedTouchedCrossings R omega C ↔ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ∧ X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C := by
-- proof
  apply StatMech.FrontierD.mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff R omega C X

/--
[mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawWiredDualHorizontalCrossingComponent R omega} :
-- imply
  Sum.inr X ∈ fkRectZeroTurnMixedTouchedCrossings R omega C ↔ ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ∧ X ∈ fkRectZeroTurnDualTouchedCrossings R omega C := by
-- proof
  apply StatMech.FrontierD.mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff R omega C X

/--
[fkRectZeroTurnMixedTouchedCrossings_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnMixedTouchedCrossings_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  (fkRectZeroTurnMixedTouchedCrossings R omega C).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnMixedTouchedCrossings_nonempty R omega C

/--
[fkRectZeroTurnSelectedMixedCrossing_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnSelectedMixedCrossing_mem_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {certificate : FKRectZeroTurnMixedTouchedCertificate R omega}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  fkRectZeroTurnSelectedMixedCrossing R omega certificate C ∈ fkRectZeroTurnMixedTouchedCrossings R omega C := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnSelectedMixedCrossing_mem R omega certificate C

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_touched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_touched_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {certificate : FKRectZeroTurnMixedTouchedCertificate R omega} :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_touched R omega certificate


-- created on 2026-10-23
