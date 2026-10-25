/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.Part4
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem
    lpReplicaAggregateRankFiveStrictRouteCandidates_card_eq_two_of_two_spatialWitnesses
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (x₀ x₁ : LPReplicaOrbitCommonSlot G sites q) (hxx : x₀ ≠ x₁)
    (hx₀ : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
      G sites q y x₀)
    (hx₁ : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
      G sites q y x₁)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (hzy : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z).card = 2 := by
  classical
  obtain ⟨d, hd⟩ := hzy
  have hx₀' : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
      G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) x₀ := by
    rw [hd]
    exact hx₀
  have hx₁' : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
      G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) x₁ := by
    rw [hd]
    exact hx₁
  obtain ⟨e₀, he₀⟩ :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness
      G sites hsite q hcard z d x₀ hx₀'
  obtain ⟨e₁, he₁⟩ :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness
      G sites hsite q hcard z d x₁ hx₁'
  have he : e₀ ≠ e₁ := by
    intro h
    apply hxx
    rw [← he₀, ← he₁, h]
  have htwo : 2 ≤
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card := by
    have heVal : e₀.1 ≠ e₁.1 := fun h => he (Subtype.ext h)
    rw [← Finset.card_pair heVal]
    apply Finset.card_le_card
    intro e heMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at heMem
    rcases heMem with rfl | rfl
    · exact e₀.2
    · exact e₁.2
  have hle :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_le_two
      G sites hsite q hcard z
  omega


theorem lpReplicaAggregateDecoratedTargetSlotState_toAggregate
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y) =
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 := by
  cases y <;> rfl

set_option maxHeartbeats 1200000 in


theorem lpReplicaRankFiveMarkedOutputData_hasStrictPhysicalDoubleIncidence_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output ↔
      LPReplicaStrictPhysicalDoubleIncidenceRaw G sites z.1.1.1
        (lpReplicaRowCopies G sites z.1.1.1
          (lpReplicaToggleRows G sites z.1.1.1 {d.copy}
            (lpReplicaDecoratedSourceRowGateData G sites i j q z).1) true) := by
  classical
  rcases d.branch with ⟨y, hy, hc⟩ | ⟨y, hy, hc⟩
  · obtain ⟨s, hp, _hL, _hP, hmove, y', _hyBal, hyState, hyPres⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
        G sites hsite hij q hcard z hthree d.copy d.copy_active hc
    have hout : d.output = Sum.inl y' := by
      rw [hy]
      apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
        G sites i j q
      apply Prod.ext
      · rfl
      · have hdState := d.state_eq
        rw [hy] at hdState
        exact hdState.trans hyState.symm
    rw [hout, LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence,
      hyPres,
      lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rcases s with ⟨sp, sorbit, stag, sgate, slabel, sselector,
      sfalse, strue, srow0, srow1⟩
    dsimp at hp hmove ⊢
    subst sp
    rw [eq_of_heq hmove]
  · obtain ⟨s, hp, _hL, _hP, hmove, y', _hyBal, hyState,
      s', hyPres, hp', hselector', htag'⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
        G sites hsite hij q hcard z hthree d.copy d.copy_active hc
    have hout : d.output = Sum.inr y' := by
      rw [hy]
      apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
        G sites i j q
      apply Prod.ext
      · rfl
      · have hdState := d.state_eq
        rw [hy] at hdState
        exact hdState.trans hyState.symm
    rw [hout, LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence,
      hyPres,
      lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rcases s with ⟨sp, sorbit, stag, sgate, slabel, sselector,
      sfalse, strue, srow0, srow1⟩
    rcases s' with ⟨sp', sorbit', stag', sgate', slabel', sselector',
      sfalse', strue', srow0', srow1'⟩
    dsimp at hp hp' hselector' htag' hmove ⊢
    subst sp
    subst sp'
    rw [eq_of_heq hselector', eq_of_heq htag', eq_of_heq hmove]


theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_exists_parallelPhysicalPair
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output) :
    let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
    ∃ c e, c ≠ e ∧ Finset.univ \ K = {c, e} ∧
      ¬ (lpReplicaCurrentFoldedEdge G sites c.1).IsDiag := by
  classical
  dsimp only
  have hraw :=
    (lpReplicaRankFiveMarkedOutputData_hasStrictPhysicalDoubleIncidence_iff
      G sites hsite hij q hcard z hhigh.1 d).mp hstrict
  obtain ⟨c, e, hce, hpair, hiff⟩ :=
    lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_singletonToggle_raw_iff
      G sites hsite hij q hcard z hhigh d.copy d.copy_active
  exact ⟨c, e, hce, hpair, hiff.mp hraw⟩

set_option maxHeartbeats 1600000 in


theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_two_spatialWitnesses
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output) :
    ∃ x₀ x₁ : LPReplicaOrbitCommonSlot G sites q, x₀ ≠ x₁ ∧
      LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q
        (lpReplicaOffdiagDecoratedTargetToAggregate
          G sites i j q d.output) x₀ ∧
      LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q
        (lpReplicaOffdiagDecoratedTargetToAggregate
          G sites i j q d.output) x₁ := by
  classical
  let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  let sourceState := lpReplicaOffdiagDecoratedSourceSlotState
    G sites i j q z
  let target := lpReplicaOffdiagDecoratedTargetToAggregate
    G sites i j q d.output
  obtain ⟨c, e, hce, hpair, hcPhysical⟩ :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_exists_parallelPhysicalPair
      G sites hsite hij q hcard z hhigh d hstrict
  have hcC : c ∈ Finset.univ \ K := by
    rw [hpair]
    simp
  have heC : e ∈ Finset.univ \ K := by
    rw [hpair]
    simp
  have hca : c ≠ d.copy := by
    intro h
    exact (Finset.mem_sdiff.mp hcC).2 (h ▸ d.copy_active)
  have hea : e ≠ d.copy := by
    intro h
    exact (Finset.mem_sdiff.mp heC).2 (h ▸ d.copy_active)
  have hparallel : c.1.1 = e.1.1 :=
    lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hhigh.1 c hcC e heC
  have hfixed : d.copy.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites := by
    rcases d.branch with ⟨_y, _hy, hc⟩ | ⟨_y, _hy, hc⟩
    · exact lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam
        G sites i z.1.1.1 d.copy hc
    · exact lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam
        G sites j z.1.1.1 d.copy hc
  have htargetState :
      lpReplicaAggregateDecoratedTargetSlotState G sites q target =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
            z.1.1.2 z.2.2 {d.copy}) sourceState := by
    exact (lpReplicaAggregateDecoratedTargetSlotState_toAggregate
      G sites i j q d.output).trans d.state_eq
  have hreflect : lpReplicaOrbitFourColorSlotReflect G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {d.copy}) sourceState = sourceState :=
    lpReplicaOrbitFourColorSlotReflect_singletonCopy_of_fixed
      G sites q z.1.1.1 z.1.1.2 z.2.2 d.copy hfixed sourceState
  have hends (x : LPReplicaOrbitCommonSlot G sites q) :
      lpReplicaOrbitFourColorSlotEnds G sites q
          (lpReplicaAggregateDecoratedTargetSlotState G sites q target) x =
        lpReplicaOrbitFourColorSlotEnds G sites q sourceState x := by
    rw [htargetState, lpReplicaOrbitFourColorSlotCrossToggle, hreflect]
    rfl
  have hrow : lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) =
        Finset.univ \ {E d.copy} := by
    rw [htargetState, lpReplicaOrbitFourColorSlotRowMask_crossToggle,
      lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
        G sites hsite hij q hcard z (Or.inr hhigh)]
    rw [lpReplicaOrbitCommonSlotsOfCopies_singleton]
    change Finset.univ ∆ {E d.copy} = Finset.univ \ {E d.copy}
    ext x
    simp [Finset.mem_symmDiff]
  have hcRow : E c ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) := by
    rw [hrow]
    simp [hca]
  have heRow : E e ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) := by
    rw [hrow]
    simp [hea]
  have hEcEe : E c ≠ E e := fun h => hce (E.injective h)
  have hcFold : ¬ (lpReplicaOrbitFoldedSlotEnds G sites q (E c)).IsDiag := by
    rw [lpReplicaOrbitFoldedSlotEnds_copy]
    exact hcPhysical
  have heFold : ¬ (lpReplicaOrbitFoldedSlotEnds G sites q (E e)).IsDiag := by
    rw [lpReplicaOrbitFoldedSlotEnds_copy]
    intro heDiag
    apply hcPhysical
    unfold lpReplicaCurrentFoldedEdge at heDiag ⊢
    rw [hparallel]
    exact heDiag
  have hendsParallel :
      lpReplicaOrbitFourColorSlotEnds G sites q sourceState (E c) =
        lpReplicaOrbitFourColorSlotEnds G sites q sourceState (E e) := by
    rw [lpReplicaOffdiagDecoratedSourceSlotEnds_copy,
      lpReplicaOffdiagDecoratedSourceSlotEnds_copy]
    unfold StatMech.Sharpness.FluxEdgeCopy.endsM
    rw [hparallel]
  refine ⟨E c, E e, hEcEe, ?_, ?_⟩
  · unfold LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
    dsimp only
    refine ⟨hcFold, hcRow, ?_⟩
    intro x hx
    refine ⟨E e, heRow, hEcEe.symm, ?_⟩
    change x ∈ lpReplicaOrbitFourColorSlotEnds G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) (E c) at hx
    change x ∈ lpReplicaOrbitFourColorSlotEnds G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) (E e)
    rw [hends] at hx
    rw [hends, ← hendsParallel]
    exact hx
  · unfold LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
    dsimp only
    refine ⟨heFold, heRow, ?_⟩
    intro x hx
    refine ⟨E c, hcRow, hEcEe, ?_⟩
    change x ∈ lpReplicaOrbitFourColorSlotEnds G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) (E e) at hx
    change x ∈ lpReplicaOrbitFourColorSlotEnds G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) (E c)
    rw [hends] at hx
    rw [hends, hendsParallel]
    exact hx


theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_incoming_degree_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output)
    (w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (hrelated : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard w
        (lpReplicaOffdiagDecoratedTargetToAggregate
          G sites i j q d.output)) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q w).card = 2 := by
  obtain ⟨x₀, x₁, hxx, hx₀, hx₁⟩ :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_two_spatialWitnesses
      G sites hsite hij q hcard z hhigh d hstrict
  exact
    lpReplicaAggregateRankFiveStrictRouteCandidates_card_eq_two_of_two_spatialWitnesses
      G sites hsite q hcard _ x₀ x₁ hxx hx₀ hx₁ w hrelated

set_option maxHeartbeats 8000000 in


theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_injective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    Function.Injective (fun d :
        ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z) =>
      lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d)) := by
  classical
  intro d e hstate
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
  change
    lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) =
      lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z e) at hstate
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


end
end StatMech.Ising
