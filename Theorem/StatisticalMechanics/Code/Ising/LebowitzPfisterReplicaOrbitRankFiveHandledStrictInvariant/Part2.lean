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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y ≠ y := by
  intro h
  have hval := congrArg
    (fun z : LPReplicaAggregateDecoratedTarget G sites q => z.1.val) h
  have hy := y.1.isLt
  simp only [lpReplicaAggregateDecoratedTargetFlipMultiplicity] at hval
  omega

@[simp] theorem lpReplicaAggregateDecoratedTargetFlipMultiplicity_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) = y := by
  rcases y with ⟨⟨n, hn⟩, tail⟩
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl <;> rfl

@[simp] theorem lpReplicaAggregateDecoratedTargetFlipMultiplicity_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) =
      lpReplicaAggregateDecoratedTargetSlotState G sites q y := by
  rfl


@[simp] theorem
    lpReplicaAggregateRankFiveStrictRouteTargetSpatialWitness_flip_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (x : LPReplicaOrbitCommonSlot G sites q) :
    LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) x ↔
      LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
        G sites q y x := by
  unfold LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
  rw [lpReplicaAggregateDecoratedTargetFlipMultiplicity_slotState]


theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incoming_degree_two
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
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output))) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q w).card = 2 := by
  obtain ⟨x₀, x₁, hxx, hx₀, hx₁⟩ :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_two_spatialWitnesses
      G sites hsite hij q hcard z hhigh d hstrict
  exact
    lpReplicaAggregateRankFiveStrictRouteCandidates_card_eq_two_of_two_spatialWitnesses
      G sites hsite q hcard _ x₀ x₁ hxx
        (lpReplicaAggregateRankFiveStrictRouteTargetSpatialWitness_flip_iff
          G sites q _ x₀ |>.mpr hx₀)
        (lpReplicaAggregateRankFiveStrictRouteTargetSpatialWitness_flip_iff
          G sites q _ x₁ |>.mpr hx₁)
        w hrelated


theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_incomingDegree_one_eq_empty
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
    LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 1
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output) = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  obtain ⟨w, hw⟩ := hnonempty
  have hwData :=
    (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
      G sites hsite q hcard 1 _ w).mp hw
  have htwo :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_incoming_degree_two
      G sites hsite hij q hcard z hhigh d hstrict w hwData.1
  omega


theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incomingDegree_one_eq_empty
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
    LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 1
          (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q
            (lpReplicaOffdiagDecoratedTargetToAggregate
              G sites i j q d.output)) = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  obtain ⟨w, hw⟩ := hnonempty
  have hwData :=
    (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
      G sites hsite q hcard 1 _ w).mp hw
  have htwo :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incoming_degree_two
      G sites hsite hij q hcard z hhigh d hstrict w hwData.1
  omega


theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_eq_half_incomingDegreeTwo
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
    (∑ w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard w
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)) =
      ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card : Real) / 2 := by
  rw [LPReplicaAggregateRankFiveStrictRouteWeight_sum_source]
  rw [lpReplicaRankFiveNonsaturatedHighMarkedOutput_incomingDegree_one_eq_empty
    G sites hsite hij q hcard z hhigh d hstrict]
  simp


theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_lt_one_iff
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
    (∑ w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard w
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)) < 1 ↔
      (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card ≤ 1 := by
  rw [lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_eq_half_incomingDegreeTwo
    G sites hsite hij q hcard z hhigh d hstrict]
  constructor
  · intro h
    have hreal : ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card : Real) < 2 := by
      linarith
    have hnat : (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card < 2 := by
      exact_mod_cast hreal
    omega
  · intro h
    have hreal : ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card : Real) ≤ 1 := by
      exact_mod_cast h
    linarith

@[simp] theorem
    lpReplicaAggregateDecoratedTargetFlipMultiplicity_hasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) ↔
      LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q y := by
  rfl

set_option maxHeartbeats 8000000 in


theorem lpReplicaAggregateRankFiveStrictRoute_exists_alternateTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hzy : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y)
    (hdegree :
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card = 2) :
    ∃ y',
      LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y' ∧
        y' ≠ y ∧
        y' ≠ lpReplicaAggregateDecoratedTargetFlipMultiplicity
          G sites q y := by
  classical
  let C :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z
  obtain ⟨d, hdTarget⟩ := hzy
  have hCtwo : C.card = 2 := hdegree
  obtain ⟨e, heC, hed⟩ := C.exists_mem_ne (by omega) d.1
  let e' : ↑C := ⟨e, heC⟩
  have hed' : e' ≠ d := by
    intro h
    exact hed (congrArg Subtype.val h)
  let y' :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
      G sites hsite q hcard z e'
  refine ⟨y', ⟨e', rfl⟩, ?_, ?_⟩
  · intro hy'y
    apply hed'
    apply
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_injective
        G sites hsite q hcard z
    exact hy'y.trans hdTarget.symm
  · intro hy'flip
    apply hed'
    apply
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_injective
        G sites hsite q hcard z
    calc
      lpReplicaAggregateDecoratedTargetSlotState G sites q
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
            G sites hsite q hcard z e') =
          lpReplicaAggregateDecoratedTargetSlotState G sites q
            (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) :=
        congrArg (lpReplicaAggregateDecoratedTargetSlotState G sites q) hy'flip
      _ = lpReplicaAggregateDecoratedTargetSlotState G sites q y := by simp
      _ = lpReplicaAggregateDecoratedTargetSlotState G sites q
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
            G sites hsite q hcard z d) :=
        congrArg (lpReplicaAggregateDecoratedTargetSlotState G sites q)
          hdTarget.symm


theorem lpReplicaAggregateDecoratedTarget_card_ge_two
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    2 ≤ Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  let yflip := lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y
  have hne : y ≠ yflip :=
    (lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne G sites q y).symm
  calc
    2 = ({y, yflip} : Finset
        (LPReplicaAggregateDecoratedTarget G sites q)).card :=
      (Finset.card_pair hne).symm
    _ ≤ (Finset.univ : Finset
        (LPReplicaAggregateDecoratedTarget G sites q)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) :=
      Finset.card_univ


theorem lpReplicaAggregateDecoratedTarget_card_ge_three_of_alternate
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y y' : LPReplicaAggregateDecoratedTarget G sites q)
    (hy'y : y' ≠ y)
    (hy'flip : y' ≠
      lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) :
    3 ≤ Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  let yflip := lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y
  have hyflip : y ≠ yflip :=
    (lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne G sites q y).symm
  have hy'mem : y' ∉ ({y, yflip} : Finset
      (LPReplicaAggregateDecoratedTarget G sites q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hy'y, hy'flip⟩
  calc
    3 = ({y', y, yflip} : Finset
        (LPReplicaAggregateDecoratedTarget G sites q)).card := by
      rw [Finset.card_insert_of_notMem hy'mem, Finset.card_pair hyflip]
    _ ≤ (Finset.univ : Finset
        (LPReplicaAggregateDecoratedTarget G sites q)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) :=
      Finset.card_univ


theorem lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    1 + (LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y).card ≤
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  let Incoming := LPReplicaAggregateRankFiveStrictRouteIncoming
    G sites hsite q hcard y
  change 1 + Incoming.card ≤
    Fintype.card (LPReplicaAggregateDecoratedTarget G sites q)
  by_cases hIncoming : Incoming.Nonempty
  · obtain ⟨z, hz⟩ := hIncoming
    have hzy : LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y :=
      (mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
        G sites hsite q hcard y z).mp hz
    obtain ⟨d, hdTarget⟩ := hzy
    have hfiber :=
      LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates
        G sites hsite q hcard y z d hdTarget
    change Incoming.card ≤
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card at hfiber
    rcases
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two
          G sites hsite q hcard z with hdegree | hdegree
    · have htarget := lpReplicaAggregateDecoratedTarget_card_ge_two
          G sites q y
      omega
    · obtain ⟨y', _hy'related, hy'y, hy'flip⟩ :=
        lpReplicaAggregateRankFiveStrictRoute_exists_alternateTarget
          G sites hsite q hcard z y ⟨d, hdTarget⟩ hdegree
      have htarget :=
        lpReplicaAggregateDecoratedTarget_card_ge_three_of_alternate
          G sites q y y' hy'y hy'flip
      omega
  · have hzero : Incoming.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hIncoming]
      rfl
    have htarget := lpReplicaAggregateDecoratedTarget_card_ge_two G sites q y
    omega


end
end StatMech.Ising
