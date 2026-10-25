/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.Part3


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 4000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    let a := z.toAggregate G sites q
    let route :=
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
        G sites hsite q hcard z d
    lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q a.2.2.2.1.1.1
          a.2.2.2.1.1.2 a.2.2.2.2.2 {route.d})
        (lpReplicaOrbitCommonSlotsOfCopies G sites q a.2.2.2.1.1.1
          a.2.2.2.1.1.2 a.2.2.2.2.2 {route.c})
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites a.1 a.2.1 q a.2.2.2) := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let route :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hdc : route.d ≠ route.c :=
    (Finset.mem_sdiff.mp route.hdK).2 ∘ Finset.mem_singleton.mpr
  have hsource : ∀ e,
      (lpReplicaDecoratedSourceRowGateData
        G sites a.1 a.2.1 q a.2.2.2).1 e = (true, false) :=
    lpReplicaOffdiagDecoratedSource_rank_five_saturated_all_falseCopies
      G sites hsite hij q hcard a.2.2.2
        (LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
          G sites hsite hij q hcard z.2.2.2.1 z.2.2.2.2).1
  let l := lpReplicaThirdOfThree a.1 a.2.1 k route.u route.v
  let Sk := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k
  let Sl := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) l
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  have hfixed : (Sl ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sl ∆ T :=
    lpReplicaCurrentReflect_seam_symmDiff_ghost G sites l
  have hraw :=
    lpReplicaOffdiagDecoratedSource_strictRoute_target_rowGate
      G sites hsite hij hik hjk route.hu route.hv route.huv q a.2.2.2
        route.c route.d route.hc hdc.symm route.hfold route.hdisc
  unfold
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
    lpReplicaAggregateDecoratedTargetSlotState
  dsimp only
  unfold lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Sk
    ((Sl ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Sl ∆ T) q hfixed]
  exact lpReplicaOffdiagDecoratedSourceCanonicalSingletonStrictRoute_slotState
    G sites a.1 a.2.1 q a.2.2.2 route.c route.d Sk (Sl ∆ T)
      hraw hsource

set_option maxHeartbeats 2000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_singletons
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    let a := z.toAggregate G sites q
    lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
        {lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q z d}
        {lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateRowSlot
          G sites hsite q z}
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites a.1 a.2.1 q a.2.2.2) := by
  dsimp only
  rw [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState]
  rw [lpReplicaOrbitCommonSlotsOfCopies_singleton,
    lpReplicaOrbitCommonSlotsOfCopies_singleton]
  rw [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d,
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c]
  rfl


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_rowMask_eq_univ
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites a.1 a.2.1 q a.2.2.2) = Finset.univ := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  exact lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
    G sites hsite hij q hcard a.2.2.2
      (LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
        G sites hsite hij q hcard z.2.2.2.1 z.2.2.2.2).1

set_option maxHeartbeats 8000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateIndices_eq_of_spatialSlot_eq_of_target_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z))
    (e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q w))
    (hspatial :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q z d =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q w e)
    (htarget :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard w e) :
    let a := z.toAggregate G sites q
    let b := w.toAggregate G sites q
    a.1 = b.1 ∧ a.2.1 = b.2.1 := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let b := w.toAggregate G sites q
  let kz := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let kw := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q b
  let routeZ :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d
  let routeW :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard w e
  have horientation := congrArg (fun y => y.1) htarget
  have hk := congrArg (fun y => y.2.1) htarget
  have hthird := congrArg (fun y => y.2.2.1) htarget
  simp only [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_orientation]
      at horientation
  simp only [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_selectedSeam]
      at hk
  simp only [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_thirdSeam]
      at hthird
  change kz = kw at hk
  change lpReplicaThirdOfThree a.1 a.2.1 kz routeZ.u routeZ.v =
    lpReplicaThirdOfThree b.1 b.2.1 kw routeW.u routeW.v at hthird
  have hfold := congrArg (lpReplicaOrbitFoldedSlotEnds G sites q) hspatial
  rw [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot_folded
      G sites hsite q hcard z d,
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot_folded
      G sites hsite q hcard w e] at hfold
  have hroute : s(routeZ.u, routeZ.v) = s(routeW.u, routeW.v) :=
    lpReplica_sitePair_eq_of_currentPhysicalPair_eq sites hsite hfold
  have hkunmarkedZ :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hkunmarkedW :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard w
  have hpair : s(a.1, a.2.1) = s(b.1, b.2.1) := by
    apply lpReplicaStrictRoute_markedPair_eq_of_third_eq_of_routePair_eq
      (k := kz) (u := routeZ.u) (v := routeZ.v)
      (u' := routeW.u) (v' := routeW.v)
    · exact lpReplicaAggregateDecoratedSource_indices_ne G sites q a
    · exact Ne.symm hkunmarkedZ.1
    · exact Ne.symm hkunmarkedZ.2
    · exact lpReplicaAggregateDecoratedSource_indices_ne G sites q b
    · simpa [hk] using Ne.symm hkunmarkedW.1
    · simpa [hk] using Ne.symm hkunmarkedW.2
    · exact routeZ.hu
    · exact routeZ.hv
    · exact routeZ.huv
    · simpa [hk] using routeW.hu
    · simpa [hk] using routeW.hv
    · exact routeW.huv
    · simpa [hk] using hthird
    · exact hroute
  have hindices : a.1 = b.1 ∧ a.2.1 = b.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_eq_of_pairCode_orientation_eq
      G sites q a b hpair horientation
  exact hindices

set_option maxHeartbeats 4000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_indices_eq_of_spatialSlot_eq_of_target_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z))
    (e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q w))
    (hindices :
      (z.toAggregate G sites q).1 = (w.toAggregate G sites q).1 ∧
        (z.toAggregate G sites q).2.1 = (w.toAggregate G sites q).2.1)
    (hspatial :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q z d =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q w e)
    (htarget :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard w e) :
    z = w := by
  classical
  have hstate := congrArg
    (lpReplicaAggregateDecoratedTargetSlotState G sites q) htarget
  rw [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_singletons,
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_singletons]
      at hstate
  have hmask := congrArg
    (lpReplicaOrbitFourColorSlotRowMask G sites q) hstate
  rw [lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle,
    lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle,
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_rowMask_eq_univ
      G sites hsite q hcard z,
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_rowMask_eq_univ
      G sites hsite q hcard w] at hmask
  have hrow := Finset.singleton_injective
    (symmDiff_right_injective (Finset.univ : Finset
      (LPReplicaOrbitCommonSlot G sites q)) hmask)
  apply LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate_injective
    G sites q
  rcases hindices with ⟨hi, hj⟩
  rcases z with ⟨i, j, zlabel, zsource, hzmem⟩
  rcases w with ⟨i', j', wlabel, wsource, hwmem⟩
  dsimp only [LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate]
    at hi hj ⊢
  subst i'
  subst j'
  have hsource : zsource = wsource := by
    apply lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision
      G sites i j q zsource wsource
      {_} {_} {_} {_}
      _ _
    · rfl
    · rfl
    · exact congrArg (fun x => ({x} : Finset _)) hspatial
    · exact congrArg (fun x => ({x} : Finset _)) hrow
    · exact hstate
  cases hsource
  have hij : i ≠ j := by
    intro hij
    subst j
    have zlabel0 : Fin 0 := by simpa using zlabel
    exact Fin.elim0 zlabel0
  have hlabel : zlabel = wlabel := by
    apply Fin.ext
    have hz := zlabel.isLt
    have hw := wlabel.isLt
    simp [hij] at hz hw
    omega
  cases hlabel
  rfl


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_spatialSlot_eq_of_target_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z))
    (e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q w))
    (hspatial :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q z d =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q w e)
    (htarget :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard w e) :
    z = w := by
  exact
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_indices_eq_of_spatialSlot_eq_of_target_eq
      G sites hsite q hcard z w d e
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateIndices_eq_of_spatialSlot_eq_of_target_eq
          G sites hsite q hcard z w d e hspatial htarget)
        hspatial htarget

set_option maxHeartbeats 8000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_injective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    Function.Injective
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard z) := by
  classical
  intro d e htarget
  let a := z.toAggregate G sites q
  let sourceState := lpReplicaOffdiagDecoratedSourceSlotState
    G sites a.1 a.2.1 q a.2.2.2
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q
    a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  let routeD :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d
  let routeE :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z e
  have hrouteDc : routeD.c = c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c
      G sites hsite q hcard z d
  have hrouteEc : routeE.c = c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c
      G sites hsite q hcard z e
  have hrouteDd : routeD.d = d.1 :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d
      G sites hsite q hcard z d
  have hrouteEd : routeE.d = e.1 :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d
      G sites hsite q hcard z e
  have hstate := congrArg
    (lpReplicaAggregateDecoratedTargetSlotState G sites q) htarget
  rw [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState,
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState]
    at hstate
  have hstate' :
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
          {E d.1} {E c} sourceState =
        lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
          {E e.1} {E c} sourceState := by
    rw [lpReplicaOrbitCommonSlotsOfCopies_singleton,
      lpReplicaOrbitCommonSlotsOfCopies_singleton,
      lpReplicaOrbitCommonSlotsOfCopies_singleton,
      lpReplicaOrbitCommonSlotsOfCopies_singleton,
      hrouteDc, hrouteEc, hrouteDd, hrouteEd] at hstate
    exact hstate
  have hdData :=
    (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
      G sites hsite q z d.1).mp d.2
  have heData :=
    (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
      G sites hsite q z e.1).mp e.2
  dsimp only at hdData heData
  have hdStrict : ∃ x, E d.1 = Sum.inr x :=
    lpReplicaProfileCopyEquivCommonSlot_eq_inr_of_folded_not_diag
      G sites q a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2 d.1
        hdData.2.2.2
  have heStrict : ∃ x, E e.1 = Sum.inr x :=
    lpReplicaProfileCopyEquivCommonSlot_eq_inr_of_folded_not_diag
      G sites q a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2 e.1
        heData.2.2.2
  apply Subtype.ext
  apply E.injective
  exact lpReplicaOrbitFourColorSlotReflectRowToggle_strictSingleton_injective
    G sites q sourceState {E c} hdStrict heStrict hstate'

set_option maxHeartbeats 2000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_hasDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) := by
  classical
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let route :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
      G sites hsite q hcard z route.c route.hc
  dsimp only at hpm
  obtain ⟨_hKcard, _hsources, _hsupport, hunique⟩ := hpm
  unfold
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
    LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
  dsimp only
  exact lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom_hasDoubleIncidence
    G sites hsite hij hik hjk route.hu route.hv route.huv q a.2.2.2
      route.c route.d route.hc route.hdK route.hfold hunique route.hdisc

end
end StatMech.Ising
