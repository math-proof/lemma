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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part5


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponentSources_card_le
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    (LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
        G sites hsite q hcard y).card ≤
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y).card := by
  classical
  let S := LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
    G sites hsite q hcard y
  let C := LPReplicaAggregateRankFiveStrictRouteRerouteComponent
    G sites hsite q hcard y
  let N := Finset.univ.filter fun target :
      LPReplicaAggregateDecoratedTarget G sites q =>
    ∃ source ∈ S, LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard source target
  have hHall : S.card ≤ N.card := by
    exact LPReplicaAggregateRankFiveStrictRouteHall
      G sites hsite q hcard S
  apply hHall.trans
  apply Finset.card_le_card
  intro t ht
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨z, hzS, hzt⟩ := ht
  have hzData : ∃ w, w ∈ C ∧
      LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z w := by
    simpa only [S, C,
      LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources,
      Finset.mem_filter, Finset.mem_univ, true_and] using hzS
  obtain ⟨w, hwC, hzw⟩ := hzData
  exact lpReplicaAggregateRankFiveStrictRouteRerouteComponent_related_mem
    G sites hsite q hcard y w t z hwC hzw hzt


theorem
    lpReplicaAggregateRankFiveStrictRoute_one_add_componentSources_card_le_of_targetLoad_lt_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y t : LPReplicaAggregateDecoratedTarget G sites q)
    (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y)
    (hslack :
      (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z t) < 1) :
    1 + (LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
        G sites hsite q hcard y).card ≤
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y).card := by
  classical
  let S := LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
    G sites hsite q hcard y
  let C := LPReplicaAggregateRankFiveStrictRouteRerouteComponent
    G sites hsite q hcard y
  let W := LPReplicaAggregateRankFiveStrictRouteWeight
    G sites hsite q hcard
  have hsourceMass (z) (hz : z ∈ S) :
      (∑ target ∈ C, W z target) = 1 := by
    rw [← LPReplicaAggregateRankFiveStrictRouteWeight_sum_target
      G sites hsite q hcard z]
    apply Finset.sum_subset (Finset.subset_univ C)
    intro target _ htarget
    apply LPReplicaAggregateRankFiveStrictRouteWeight_eq_zero_of_not_related
    intro hzt
    have hzData : ∃ w, w ∈ C ∧
        LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z w := by
      simpa only [S, C,
        LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources,
        Finset.mem_filter, Finset.mem_univ, true_and] using hz
    obtain ⟨w, hw, hzw⟩ := hzData
    exact htarget
      (lpReplicaAggregateRankFiveStrictRouteRerouteComponent_related_mem
        G sites hsite q hcard y w target z hw hzw hzt)
  have htargetMass (target) (htarget : target ∈ C) :
      (∑ z ∈ S, W z target) ≤ 1 := by
    calc
      (∑ z ∈ S, W z target) ≤ ∑ z, W z target := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ S)
          (fun z _ _ =>
            LPReplicaAggregateRankFiveStrictRouteWeight_nonneg
              G sites hsite q hcard z target)
      _ ≤ 1 := lpReplicaAggregateRankFiveStrictRouteTargetLoad
        G sites hsite q hcard target
  have hrestrictedSlack : (∑ z ∈ S, W z t) < 1 := by
    apply lt_of_le_of_lt _ hslack
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S)
      (fun z _ _ =>
        LPReplicaAggregateRankFiveStrictRouteWeight_nonneg
          G sites hsite q hcard z t)
  have hlt : S.card < C.card :=
    finiteSubset_card_lt_of_fractionalWeights_of_target_slack
      W S C hsourceMass htargetMass t ht hrestrictedSlack
  change 1 + S.card ≤ C.card
  omega


end
end StatMech.Ising
