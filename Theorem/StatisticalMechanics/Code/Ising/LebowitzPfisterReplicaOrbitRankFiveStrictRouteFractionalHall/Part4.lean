/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.FractionalHall
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.Part5


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_integer
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateRankFiveStrictRouteTargetLoad
        G sites hsite q hcard ↔
      ∀ y : LPReplicaAggregateDecoratedTarget G sites q,
        2 * (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 1 y).card +
          (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 2 y).card ≤ 2 := by
  constructor
  · intro hload y
    have hy := hload y
    rw [LPReplicaAggregateRankFiveStrictRouteWeight_sum_source] at hy
    have hreal :
        (2 : Real) *
            ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 1 y).card : Real) +
          ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 2 y).card : Real) ≤ 2 := by
      linarith [hy]
    exact_mod_cast hreal
  · intro hinteger
    unfold LPReplicaAggregateRankFiveStrictRouteTargetLoad
    intro y
    rw [LPReplicaAggregateRankFiveStrictRouteWeight_sum_source]
    have hreal :
        (2 : Real) *
            ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 1 y).card : Real) +
          ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 2 y).card : Real) ≤ 2 := by
      exact_mod_cast hinteger y
    linarith


theorem LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_classification
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateRankFiveStrictRouteTargetLoad
        G sites hsite q hcard ↔
      ∀ y : LPReplicaAggregateDecoratedTarget G sites q,
        ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 1 y).card = 0 ∧
            (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 2 y).card ≤ 2) ∨
          ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
                G sites hsite q hcard 1 y).card = 1 ∧
            (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 2 y).card = 0) := by
  rw [LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_integer]
  constructor
  · intro h y
    specialize h y
    omega
  · intro h y
    rcases h y with h | h <;> omega


theorem LPReplicaAggregateRankFiveStrictRouteIncoming_classification
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 1 y).card = 0 ∧
        (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 2 y).card ≤ 2) ∨
      ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 1 y).card = 1 ∧
        (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 2 y).card = 0) := by
  classical
  let D1 := LPReplicaAggregateRankFiveStrictRouteIncomingDegree
    G sites hsite q hcard 1 y
  let D2 := LPReplicaAggregateRankFiveStrictRouteIncomingDegree
    G sites hsite q hcard 2 y
  let Incoming := LPReplicaAggregateRankFiveStrictRouteIncoming
    G sites hsite q hcard y
  have hsub1 : D1 ⊆ Incoming := by
    exact LPReplicaAggregateRankFiveStrictRouteIncomingDegree_subset_incoming
      G sites hsite q hcard 1 y
  have hsub2 : D2 ⊆ Incoming := by
    exact LPReplicaAggregateRankFiveStrictRouteIncomingDegree_subset_incoming
      G sites hsite q hcard 2 y
  by_cases h1 : D1.Nonempty
  · obtain ⟨z, hz1⟩ := h1
    have hzData :=
      (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
        G sites hsite q hcard 1 y z).mp hz1
    obtain ⟨d, hdTarget⟩ := hzData.1
    have hIncoming :=
      LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates
        G sites hsite q hcard y z d hdTarget
    change Incoming.card ≤
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card at hIncoming
    rw [hzData.2] at hIncoming
    have hD1le : D1.card ≤ 1 :=
      (Finset.card_le_card hsub1).trans hIncoming
    have hD1pos : 0 < D1.card := Finset.card_pos.mpr ⟨z, hz1⟩
    have hD1 : D1.card = 1 := by omega
    have hD2 : D2.card = 0 := by
      by_contra hne
      have hpos : 0 < D2.card := Nat.pos_of_ne_zero hne
      obtain ⟨w, hw2⟩ := Finset.card_pos.mp hpos
      have hwData :=
        (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
          G sites hsite q hcard 2 y w).mp hw2
      have hwz : w = z := Finset.card_le_one.mp hIncoming
        w (hsub2 hw2) z (hsub1 hz1)
      subst w
      omega
    exact Or.inr ⟨hD1, hD2⟩
  · have hD1 : D1.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp h1]
      rfl
    have hD2 : D2.card ≤ 2 := by
      by_cases h2 : D2.Nonempty
      · obtain ⟨z, hz2⟩ := h2
        have hzData :=
          (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
            G sites hsite q hcard 2 y z).mp hz2
        obtain ⟨d, hdTarget⟩ := hzData.1
        have hIncoming :=
          LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates
            G sites hsite q hcard y z d hdTarget
        change Incoming.card ≤
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
            G sites hsite q z).card at hIncoming
        rw [hzData.2] at hIncoming
        exact (Finset.card_le_card hsub2).trans hIncoming
      · rw [Finset.not_nonempty_iff_eq_empty.mp h2]
        simp
    exact Or.inl ⟨hD1, hD2⟩


theorem lpReplicaAggregateRankFiveStrictRouteTargetLoad
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateRankFiveStrictRouteTargetLoad
      G sites hsite q hcard := by
  rw [LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_classification]
  exact LPReplicaAggregateRankFiveStrictRouteIncoming_classification
    G sites hsite q hcard


theorem LPReplicaAggregateRankFiveStrictRouteHall_of_targetLoad
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (hload : LPReplicaAggregateRankFiveStrictRouteTargetLoad
      G sites hsite q hcard) :
    ∀ sources : Finset
        (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q),
      sources.card ≤
        (Finset.univ.filter fun target :
          LPReplicaAggregateDecoratedTarget G sites q =>
            ∃ source ∈ sources,
              LPReplicaAggregateRankFiveStrictRouteRelated
                G sites hsite q hcard source target).card := by
  classical
  apply finiteRelationHall_of_fractionalWeights
    (LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard)
    (LPReplicaAggregateRankFiveStrictRouteWeight
      G sites hsite q hcard)
  · exact LPReplicaAggregateRankFiveStrictRouteWeight_nonneg
      G sites hsite q hcard
  · exact LPReplicaAggregateRankFiveStrictRouteWeight_eq_zero_of_not_related
      G sites hsite q hcard
  · intro source
    rw [LPReplicaAggregateRankFiveStrictRouteWeight_sum_target
      G sites hsite q hcard source]
  · exact hload


theorem LPReplicaAggregateRankFiveStrictRouteHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    ∀ sources : Finset
        (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q),
      sources.card ≤
        (Finset.univ.filter fun target :
          LPReplicaAggregateDecoratedTarget G sites q =>
            ∃ source ∈ sources,
              LPReplicaAggregateRankFiveStrictRouteRelated
                G sites hsite q hcard source target).card :=
  LPReplicaAggregateRankFiveStrictRouteHall_of_targetLoad
    G sites hsite q hcard
      (lpReplicaAggregateRankFiveStrictRouteTargetLoad
        G sites hsite q hcard)

end
end StatMech.Ising
