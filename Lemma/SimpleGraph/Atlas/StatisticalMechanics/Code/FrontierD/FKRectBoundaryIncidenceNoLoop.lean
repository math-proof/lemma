import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part8
open StatMech StatMech.FrontierD


/--
[fkRectForcedDualSameSideRightBoundaryConnected_of_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectForcedDualSameSideRightBoundaryConnected_of_reflection_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hreflect : FKRectForcedDualSameSideRightBoundaryConnectivityReflection R omega) :
-- imply
  FKRectForcedDualSameSideRightBoundaryConnected R omega := by
-- proof
  apply StatMech.FrontierD.fkRectForcedDualSameSideRightBoundaryConnected_of_reflection R omega hreflect

/--
[fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_rightBoundaryContacts_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_rightBoundaryContacts_reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectZeroTurnCutRemainderComponent R omega}
  {yC yD : Fin R.height}
-- given
  (hyC : yC ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C)
  (hyD : yD ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D)
  (hyCD : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Reachable (fkRectRightColumn R, yC) (fkRectRightColumn R, yD)) :
-- imply
  fkRectBlackBoundaryCyclePrimalComponent R (fkRectDualConfigurationEquiv R omega) (fkRectBlackBoundaryCycleDualEquiv R omega (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) = fkRectBlackBoundaryCyclePrimalComponent R (fkRectDualConfigurationEquiv R omega) (fkRectBlackBoundaryCycleDualEquiv R omega (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D))) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_rightBoundaryContacts_reachable R omega C D yC yD hyC hyD hyCD

/--
[fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_sharedRightBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_sharedRightBoundaryContact_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectZeroTurnCutRemainderComponent R omega}
  {y : Fin R.height}
-- given
  (hyC : y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C)
  (hyD : y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D) :
-- imply
  fkRectBlackBoundaryCyclePrimalComponent R (fkRectDualConfigurationEquiv R omega) (fkRectBlackBoundaryCycleDualEquiv R omega (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) = fkRectBlackBoundaryCyclePrimalComponent R (fkRectDualConfigurationEquiv R omega) (fkRectBlackBoundaryCycleDualEquiv R omega (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D))) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_sharedRightBoundaryContact R omega C D y hyC hyD

/--
[fkRectBlackBoundaryCycle_eq_of_primalComponent_eq_of_fst_mul_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycle_eq_of_primalComponent_eq_of_fst_mul_pos_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectConfigurationBlackBoundaryCycle R omega}
-- given
  (hcomponent : fkRectBlackBoundaryCyclePrimalComponent R omega C = fkRectBlackBoundaryCyclePrimalComponent R omega D)
  (hsign : 0 < (fkRectBlackBoundaryCycleWinding R omega C).1 * (fkRectBlackBoundaryCycleWinding R omega D).1) :
-- imply
  C = D := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycle_eq_of_primalComponent_eq_of_fst_mul_pos R omega C D hcomponent hsign

/--
[fkRectZeroTurnRemainderBlackDart_fst_mul_pos_of_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderBlackDart_fst_mul_pos_of_sameSide_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hside : fkRectZeroTurnRemainderSide R omega C = fkRectZeroTurnRemainderSide R omega D) :
-- imply
  0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C))).1 * (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega D))).1 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderBlackDart_fst_mul_pos_of_sameSide R omega C D hside

/--
[fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hcomponent : fkRectZeroTurnRemainderPrimalComponent R omega C = fkRectZeroTurnRemainderPrimalComponent R omega D)
  (hside : fkRectZeroTurnRemainderSide R omega C = fkRectZeroTurnRemainderSide R omega D) :
-- imply
  C = D := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide R omega C D hcomponent hside

/--
[fkRectZeroTurnRemainder_eq_of_dualComponent_eq_of_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainder_eq_of_dualComponent_eq_of_sameSide_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hcomponent : fkRectBlackBoundaryCyclePrimalComponent R (fkRectDualConfigurationEquiv R omega) (fkRectBlackBoundaryCycleDualEquiv R omega (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) = fkRectBlackBoundaryCyclePrimalComponent R (fkRectDualConfigurationEquiv R omega) (fkRectBlackBoundaryCycleDualEquiv R omega (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D))))
  (hside : fkRectZeroTurnRemainderSide R omega C = fkRectZeroTurnRemainderSide R omega D) :
-- imply
  C = D := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainder_eq_of_dualComponent_eq_of_sameSide R omega C D hcomponent hside

/--
[fkRectZeroTurnSelectedPrimalTouchedCrossing_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnSelectedPrimalTouchedCrossing_mem_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
-- imply
  fkRectZeroTurnSelectedPrimalTouchedCrossing R omega C hC ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnSelectedPrimalTouchedCrossing_mem R omega C hC

/--
[fkRectZeroTurnSelectedDualRightBoundaryContact_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnSelectedDualRightBoundaryContact_mem_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  fkRectZeroTurnSelectedDualRightBoundaryContact R omega C ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnSelectedDualRightBoundaryContact_mem R omega C

/--
[fkRectZeroTurnSelectedPrimalOrRightBoundaryContact_side_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnSelectedPrimalOrRightBoundaryContact_side_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Function.Injective fun C : FKRectZeroTurnCutRemainderComponent R omega => (fkRectZeroTurnSelectedPrimalOrRightBoundaryContact R omega C, fkRectZeroTurnRemainderSide R omega C) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnSelectedPrimalOrRightBoundaryContact_side_injective R omega

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_height_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_height_unconditional_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) + 2 * R.height := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_height_unconditional R omega

/--
[fkRect_not_crossesVerticalSeam_indexedEdge_of_not_mem_horizontalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRect_not_crossesVerticalSeam_indexedEdge_of_not_mem_horizontalCut_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex}
-- given
  (ha : a ∉ fkRectHorizontalCutEdges R) :
-- imply
  ¬ fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
-- proof
  apply StatMech.FrontierD.fkRect_not_crossesVerticalSeam_indexedEdge_of_not_mem_horizontalCut R a ha

/--
[exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
-- imply
  ∃ a : R.EdgeIndex, a ∈ fkRectHorizontalCutEdges R ∧ fkRectTorusIndexedEdge R a ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C)).edges := by
-- proof
  apply StatMech.FrontierD.exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk R omega C hC

/--
[fkRectZeroTurnSelectedHorizontalCutEdge_mem_boundaryCycleWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnSelectedHorizontalCutEdge_mem_boundaryCycleWalk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
-- imply
  fkRectTorusIndexedEdge R (fkRectZeroTurnSelectedHorizontalCutEdge R omega C hC).1 ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C)).edges := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnSelectedHorizontalCutEdge_mem_boundaryCycleWalk R omega C hC

/--
[fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_boundaryEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_boundaryEdge_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectZeroTurnCutRemainderComponent R omega}
  {a : R.EdgeIndex}
-- given
  (haC : fkRectTorusIndexedEdge R a ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C)).edges)
  (haD : fkRectTorusIndexedEdge R a ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega D)).edges) :
-- imply
  fkRectZeroTurnRemainderPrimalComponent R omega C = fkRectZeroTurnRemainderPrimalComponent R omega D := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_boundaryEdge R omega C D a haC haD

/--
[fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge_side_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge_side_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Function.Injective fun C : FKRectZeroTurnCutRemainderComponent R omega => (fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge R omega C, fkRectZeroTurnRemainderSide R omega C) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge_side_injective R omega

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_four_width_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_four_width_unconditional_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) + 4 * R.width := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_four_width_unconditional R omega

/--
[fkRectCritical_zeroTurnAbove_le_half_of_boundaryIncidenceAdaptiveTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_half_of_boundaryIncidenceAdaptiveTail_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q)
  (hsmall : Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  fkRectCriticalZeroTurnAboveMass R q (2 * R.width + (4 * R.width + 2 * n)) ≤ (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_half_of_boundaryIncidenceAdaptiveTail R hq n hsmall

/--
[tendsto_allSectorNormalization_negLog_div_height_zero_of_boundaryIncidenceAdaptiveTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma tendsto_allSectorNormalization_negLog_div_height_zero_of_boundaryIncidenceAdaptiveTail_eq
  {R : Nat → FKRectTorus}
  {q : Real}
  {n : Nat → Nat}
-- given
  (hq : 4 < q)
  (hsmall : ∀ k, Nat.choose (R k).height (n k + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 ((R k).width - 2))) ^ (n k + 1) ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * (R k).width + (R k).height) / 2)
  (hwidth : Tendsto (fun k ↦ ((R k).width : Real) / (R k).height) atTop (nhds 0))
  (hn : Tendsto (fun k ↦ (n k : Real) / (R k).height) atTop (nhds 0))
  (hheight : Tendsto (fun k ↦ (R k).height) atTop atTop) :
-- imply
  Tendsto (fun k ↦ -Real.log (fkRectAllSectorNormalization (R k) q) / (R k).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_allSectorNormalization_negLog_div_height_zero_of_boundaryIncidenceAdaptiveTail R hq n hsmall hwidth hn hheight

/--
[fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnected_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hconnected : FKRectForcedDualSameSideRightBoundaryConnected R omega) :
-- imply
  FKRectForcedDualSameSideOriginalComponent R omega := by
-- proof
  apply StatMech.FrontierD.fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnected R omega hconnected

/--
[fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnectivityReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnectivityReflection_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hreflect : FKRectForcedDualSameSideRightBoundaryConnectivityReflection R omega) :
-- imply
  FKRectForcedDualSameSideOriginalComponent R omega := by
-- proof
  apply StatMech.FrontierD.fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnectivityReflection R omega hreflect

/--
[fkRectForcedDualSameSideOriginalComponent_of_sharedRightBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectForcedDualSameSideOriginalComponent_of_sharedRightBoundaryContact_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hcontact : FKRectForcedDualSameSideSharedRightBoundaryContact R omega) :
-- imply
  FKRectForcedDualSameSideOriginalComponent R omega := by
-- proof
  apply StatMech.FrontierD.fkRectForcedDualSameSideOriginalComponent_of_sharedRightBoundaryContact R omega hcontact

/--
[fkRectZeroTurnOriginalDualSameSideUnique_of_originalComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnOriginalDualSameSideUnique_of_originalComponent_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hcomponent : FKRectForcedDualSameSideOriginalComponent R omega) :
-- imply
  FKRectZeroTurnOriginalDualSameSideUnique R omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnOriginalDualSameSideUnique_of_originalComponent R omega hcomponent

/--
[fkRectZeroTurnOriginalDualSameSideUnique_of_rightBoundaryConnectivityReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectZeroTurnOriginalDualSameSideUnique_of_rightBoundaryConnectivityReflection_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hreflect : FKRectForcedDualSameSideRightBoundaryConnectivityReflection R omega) :
-- imply
  FKRectZeroTurnOriginalDualSameSideUnique R omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnOriginalDualSameSideUnique_of_rightBoundaryConnectivityReflection R omega hreflect

/--
[fkRectPrimalBoundaryFiberSameSignUnique_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma fkRectPrimalBoundaryFiberSameSignUnique_unconditional_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  FKRectPrimalBoundaryFiberSameSignUnique R omega := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalBoundaryFiberSameSignUnique_unconditional R omega

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_boundaryIncidence_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_boundaryIncidence_height_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q)
  (hextreme : forall omega : R.Configuration, FKRectPrimalDevelopedExtremeSameSign R omega)
  (hdual : forall omega : R.Configuration, FKRectZeroTurnOriginalDualSameSideUnique R omega) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) <= fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_boundaryIncidence_height R hq hextreme hdual


-- created on 2026-10-23
