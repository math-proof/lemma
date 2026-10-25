import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNormalRotatedSlack.Part3
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_currentSuccessorMarginIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma exists_currentSuccessorMarginIndex_eq
-- given
  (horizontal vertical : Nat -> Nat)
  (hhorizontal : Tendsto horizontal atTop atTop)
  (hvertical : Tendsto vertical atTop atTop)
  (horizontalRequirement verticalRequirement : Fin 8 -> Int) :
-- imply
  exists k, (forall i, horizontalRequirement i <= horizontal k) /\ (forall i, horizontalRequirement i <= horizontal (k + 1)) /\ (forall i, verticalRequirement i <= vertical k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_currentSuccessorMarginIndex horizontal vertical hhorizontal hvertical horizontalRequirement verticalRequirement

/--
[PeriodicPlaneEmbedding.orbitBoxCoordinateBound_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma orbitBoxCoordinateBound_mono_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {n m : Nat}
  {i : Fin 2}
-- given
  (hnm : n <= m) :
-- imply
  E.orbitBoxCoordinateBound n i <= E.orbitBoxCoordinateBound m i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.orbitBoxCoordinateBound_mono E hnm i

/--
[PeriodicPlaneEmbedding.connectorMarginRequirement_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma connectorMarginRequirement_mono_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {radius radius' : Nat}
-- given
  (h : radius <= radius') :
-- imply
  E.connectorMarginRequirement radius <= E.connectorMarginRequirement radius' := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.connectorMarginRequirement_mono E h

/--
[PeriodicPlaneEmbedding.axisSwap_horizontalCrossingEvent_subset_verticalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma axisSwap_horizontalCrossingEvent_subset_verticalCrossingEvent_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real} :
-- imply
  E.axisSwap.horizontalCrossingEvent a b c d ⊆ E.verticalCrossingEvent c d a b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_horizontalCrossingEvent_subset_verticalCrossingEvent E a b c d

/--
[PeriodicPlaneEmbedding.axisSwap_crossingMax_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma axisSwap_crossingMax_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (aH bH cH dH aV bV cV dV : Nat -> Real)
  (hlimit : Tendsto (fun n => max (mu.real (E.axisSwap.horizontalCrossingEvent (aH n) (bH n) (cH n) (dH n))) (mu.real (E.axisSwap.verticalCrossingEvent (aV n) (bV n) (cV n) (dV n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (cH n) (dH n) (aH n) (bH n))) (mu.real (E.horizontalCrossingEvent (cV n) (dV n) (aV n) (bV n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_crossingMax_tendsto_one E mu aH bH cH dH aV bV cV dV hlimit

/--
[PairedAlignedConnectorSlack.of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma of_le_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {radius radius' k : Nat}
  {slack : PairedAlignedConnectorSlack E Edual family familyDual schedule radius' k}
-- given
  (h : radius <= radius') :
-- imply
  PairedAlignedConnectorSlack E Edual family familyDual schedule radius k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAlignedConnectorSlack.of_le E Edual h slack

/--
[tendsto_two_max_one_fixedBranches_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma tendsto_two_max_one_fixedBranches_subsequence_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (H0 V1 V0 H1 : Nat -> Real)
  (hnormal : Tendsto (fun n => max (H0 n) (V1 n)) atTop (nhds 1))
  (hrotated : Tendsto (fun n => max (V0 n) (H1 n)) atTop (nhds 1)) :
-- imply
  (exists phi : Nat -> Nat, StrictMono phi /\ Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/ (exists phi : Nat -> Nat, StrictMono phi /\ Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) \/ (exists phi : Nat -> Nat, StrictMono phi /\ Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/ (exists phi : Nat -> Nat, StrictMono phi /\ Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.tendsto_two_max_one_fixedBranches_subsequence H0 V1 V0 H1 hnormal hrotated

/--
[exists_pairedAlignedNormalRotatedConnectorSlack](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma exists_pairedAlignedNormalRotatedConnectorSlack_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {radius radiusRotated : Nat} :
-- imply
  exists k, PairedAlignedConnectorSlack E Edual family familyDual schedule radius k /\ PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap family.axisSwap familyDual.axisSwap schedule.axisSwap radiusRotated k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedAlignedNormalRotatedConnectorSlack E Edual family familyDual schedule radius radiusRotated

/--
[PeriodicPlaneEmbedding.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
-- given
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (p pDual : Nat -> Real)
  (schedule : forall n, PairedAlignedMarginSchedule E Edual (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
  (hpDual : Tendsto pDual atTop (nhds 1))
  (hpDual_le : forall n, pDual n <= 1) :
-- imply
  exists radius : Nat -> Nat, forall (k extentX extentY : Nat -> Nat) (data : forall n, AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n) (family n) (familyDual n) (schedule n) (k n) (extentX n) (extentY n)), (forall n, PairedAlignedConnectorSlack E Edual (family n) (familyDual n) (schedule n) (max (radius n) n) (k n)) -> Tendsto (fun n => max (muDual.real (Edual.horizontalCrossingEvent 0 (extentX n) 0 (extentY n))) (muDual.real (Edual.verticalCrossingEvent (data n).raw.data.wideLeft (data n).raw.data.wideRight 0 (extentY n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit E Edual mu muDual hFKGDual hTIDual huniqueDual p pDual family familyDual schedule hpDual hpDual_le

/--
[NormalRotatedInsetLimitData.normalWideInset_eq_rotatedY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma normalWideInset_eq_rotatedY_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {padding : Nat}
  {data : NormalRotatedInsetLimitData E Edual mu muDual padding}
  {n : Nat} :
-- imply
  (data.level n).normal.raw.wideLeftInt + padding + (data.level n).rotatedY = (data.level n).normal.raw.wideRightInt - padding := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalRotatedInsetLimitData.normalWideInset_eq_rotatedY data n

/--
[NormalRotatedInsetLimitData.normalWideInset_real_eq_rotatedY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma normalWideInset_real_eq_rotatedY_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {padding : Nat}
  {data : NormalRotatedInsetLimitData E Edual mu muDual padding}
  {n : Nat} :
-- imply
  (data.level n).normal.raw.data.wideLeft + padding + (data.level n).rotatedY = (data.level n).normal.raw.data.wideRight - padding := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalRotatedInsetLimitData.normalWideInset_real_eq_rotatedY data n

/--
[NormalRotatedInsetLimitData.rotatedWideRight_eq_left_add_normalY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma rotatedWideRight_eq_left_add_normalY_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {padding : Nat}
  {data : NormalRotatedInsetLimitData E Edual mu muDual padding}
  {n : Nat} :
-- imply
  (data.level n).rotated.raw.wideRightInt = (data.level n).rotated.raw.wideLeftInt + (data.level n).normalY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalRotatedInsetLimitData.rotatedWideRight_eq_left_add_normalY data n

/--
[NormalRotatedInsetLimitData.rotatedWide_real_eq_normalY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma rotatedWide_real_eq_normalY_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {padding : Nat}
  {data : NormalRotatedInsetLimitData E Edual mu muDual padding}
  {n : Nat} :
-- imply
  (data.level n).rotated.raw.data.wideRight = (data.level n).rotated.raw.data.wideLeft + (data.level n).normalY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalRotatedInsetLimitData.rotatedWide_real_eq_normalY data n

/--
[NormalRotatedInsetLimitData.rotatedX_le_normalY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma rotatedX_le_normalY_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {padding : Nat}
  {data : NormalRotatedInsetLimitData E Edual mu muDual padding}
  {n : Nat} :
-- imply
  (data.level n).rotatedX <= (data.level n).normalY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalRotatedInsetLimitData.rotatedX_le_normalY data n

/--
[NormalRotatedInsetLimitData.rotatedOriginalLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma rotatedOriginalLimit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {padding : Nat}
  {data : NormalRotatedInsetLimitData E Edual mu muDual padding} :
-- imply
  Tendsto (fun n => max (mu.real (E.verticalCrossingEvent 0 (data.level n).rotatedY 0 (data.level n).rotatedX)) (mu.real (E.horizontalCrossingEvent 0 (data.level n).rotatedY (data.rotatedLevel n).raw.data.wideLeft (data.rotatedLevel n).raw.data.wideRight))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalRotatedInsetLimitData.rotatedOriginalLimit data

/--
[NormalRotatedInsetLimitData.dualRotatedOriginalLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma dualRotatedOriginalLimit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {padding : Nat}
  {data : NormalRotatedInsetLimitData E Edual mu muDual padding} :
-- imply
  Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent 0 (data.level n).rotatedY 0 (data.level n).rotatedX)) (muDual.real (Edual.horizontalCrossingEvent 0 (data.level n).rotatedY (data.rotatedLevel n).raw.data.wideLeft (data.rotatedLevel n).raw.data.wideRight))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalRotatedInsetLimitData.dualRotatedOriginalLimit data

/--
[NormalRotatedInsetLimitData.exists_primalDualFixedBranchesSubsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma exists_primalDualFixedBranchesSubsequence_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {padding : Nat}
  {data : NormalRotatedInsetLimitData E Edual mu muDual padding} :
-- imply
  let H0 : Nat -> Real := fun n => mu.real (E.horizontalCrossingEvent 0 (data.level n).normalX 0 (data.level n).normalY) let V1 : Nat -> Real := fun n => mu.real (E.verticalCrossingEvent (data.level n).normal.raw.data.wideLeft (data.level n).normal.raw.data.wideRight 0 (data.level n).normalY) let V0 : Nat -> Real := fun n => muDual.real (Edual.verticalCrossingEvent 0 (data.level n).rotatedY 0 (data.level n).rotatedX) let H1 : Nat -> Real := fun n => muDual.real (Edual.horizontalCrossingEvent 0 (data.level n).rotatedY (data.rotatedLevel n).raw.data.wideLeft (data.rotatedLevel n).raw.data.wideRight) (exists phi : Nat -> Nat, StrictMono phi /\ Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/ (exists phi : Nat -> Nat, StrictMono phi /\ Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) \/ (exists phi : Nat -> Nat, StrictMono phi /\ Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/ (exists phi : Nat -> Nat, StrictMono phi /\ Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalRotatedInsetLimitData.exists_primalDualFixedBranchesSubsequence data

/--
[nonempty_normalRotatedInsetLimitData_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma nonempty_normalRotatedInsetLimitData_of_unique_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {padding : Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
-- imply
  Nonempty (NormalRotatedInsetLimitData E Edual mu muDual padding) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_normalRotatedInsetLimitData_of_unique E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual padding

/--
[NormalTwoRotatedEndpointLimitData.normalWide_real_span_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma normalWide_real_span_eq_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {data : NormalTwoRotatedEndpointLimitData E Edual mu muDual}
  {n : Nat} :
-- imply
  (data.level n).normal.raw.data.wideRight - (data.level n).normal.raw.data.wideLeft = (data.level n).rotatedHorizontalY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalTwoRotatedEndpointLimitData.normalWide_real_span_eq data n

/--
[NormalTwoRotatedEndpointLimitData.rotatedHorizontalWide_real_span_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma rotatedHorizontalWide_real_span_eq_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {data : NormalTwoRotatedEndpointLimitData E Edual mu muDual}
  {n : Nat} :
-- imply
  (data.level n).rotatedHorizontal.raw.data.wideRight - (data.level n).rotatedHorizontal.raw.data.wideLeft = (data.level n).normalY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalTwoRotatedEndpointLimitData.rotatedHorizontalWide_real_span_eq data n

/--
[NormalTwoRotatedEndpointLimitData.dualRotatedVerticalOriginalLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma dualRotatedVerticalOriginalLimit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {data : NormalTwoRotatedEndpointLimitData E Edual mu muDual} :
-- imply
  Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent 0 (data.level n).normalX 0 (data.level n).normalY)) (muDual.real (Edual.horizontalCrossingEvent 0 (data.level n).normalX (data.rotatedVerticalLevel n).raw.data.wideLeft (data.rotatedVerticalLevel n).raw.data.wideRight))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalTwoRotatedEndpointLimitData.dualRotatedVerticalOriginalLimit data

/--
[NormalTwoRotatedEndpointLimitData.dualRotatedHorizontalOriginalLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma dualRotatedHorizontalOriginalLimit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {data : NormalTwoRotatedEndpointLimitData E Edual mu muDual} :
-- imply
  Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent 0 (data.level n).rotatedHorizontalY 0 (data.level n).rotatedHorizontalX)) (muDual.real (Edual.horizontalCrossingEvent 0 (data.level n).rotatedHorizontalY (data.rotatedHorizontalLevel n).raw.data.wideLeft (data.rotatedHorizontalLevel n).raw.data.wideRight))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalTwoRotatedEndpointLimitData.dualRotatedHorizontalOriginalLimit data

/--
[nonempty_normalTwoRotatedEndpointLimitData_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean)
-/
@[path]
private lemma nonempty_normalTwoRotatedEndpointLimitData_of_unique_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
-- imply
  Nonempty (NormalTwoRotatedEndpointLimitData E Edual mu muDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_normalTwoRotatedEndpointLimitData_of_unique E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual


-- created on 2026-10-23
