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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part6


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y y' : LPReplicaAggregateDecoratedTarget G sites q)
    (hy' : y' = y ∨ y' =
      lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) :
    y' ∈ LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
      G sites hsite q hcard y := by
  rcases hy' with rfl | rfl <;>
    simp [LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood]


theorem
    lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_rerouteNeighborhood
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    1 + (LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y).card ≤
      (LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
        G sites hsite q hcard y).card := by
  classical
  let Incoming := LPReplicaAggregateRankFiveStrictRouteIncoming
    G sites hsite q hcard y
  let N := LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
    G sites hsite q hcard y
  change 1 + Incoming.card ≤ N.card
  have hpair : 2 ≤ N.card := by
    let yflip := lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y
    have hne : y ≠ yflip :=
      (lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne G sites q y).symm
    calc
      2 = ({y, yflip} : Finset
          (LPReplicaAggregateDecoratedTarget G sites q)).card :=
        (Finset.card_pair hne).symm
      _ ≤ N.card := Finset.card_le_card
        (by
          intro y' hy'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
          exact
            lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood
              G sites hsite q hcard y y' hy')
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
    · omega
    · obtain ⟨y', hy'related, hy'y, hy'flip⟩ :=
        lpReplicaAggregateRankFiveStrictRoute_exists_alternateTarget
          G sites hsite q hcard z y ⟨d, hdTarget⟩ hdegree
      have hy'mem : y' ∈ N := by
        change y' ∈ LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
          G sites hsite q hcard y
        simp only [LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood,
          Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr (Or.inr ⟨z, hz, hy'related⟩)
      have hthree : 3 ≤ N.card := by
        let yflip :=
          lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y
        have hyflip : y ≠ yflip :=
          (lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne
            G sites q y).symm
        have hy'pair : y' ∉ ({y, yflip} : Finset
            (LPReplicaAggregateDecoratedTarget G sites q)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hy'y, hy'flip⟩
        calc
          3 = ({y', y, yflip} : Finset
              (LPReplicaAggregateDecoratedTarget G sites q)).card := by
            rw [Finset.card_insert_of_notMem hy'pair,
              Finset.card_pair hyflip]
          _ ≤ N.card := Finset.card_le_card (by
            intro t ht
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with ht | ht | ht
            · rw [ht]
              exact hy'mem
            · exact
                (lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood
                  G sites hsite q hcard y t) (Or.inl ht)
            · exact
                (lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood
                  G sites hsite q hcard y t) (Or.inr ht))
      omega
  · have hzero : Incoming.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hIncoming]
      rfl
    omega


end
end StatMech.Ising
