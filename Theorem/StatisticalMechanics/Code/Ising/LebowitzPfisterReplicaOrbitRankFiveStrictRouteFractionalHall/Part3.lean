/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.FractionalHall
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.Part4


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    z ∈ LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y ↔
      LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y := by
  classical
  simp [LPReplicaAggregateRankFiveStrictRouteIncoming]


theorem LPReplicaAggregateRankFiveStrictRouteIncomingDegree_subset_incoming
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (degree : Nat) (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard degree y ⊆
      LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y := by
  intro z hz
  rw [mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff]
  exact (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
    G sites hsite q hcard degree y z).mp hz |>.1

set_option maxHeartbeats 8000000 in


theorem LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z))
    (hzd :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard z d = y) :
    (LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y).card ≤
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card := by
  classical
  let Incoming := LPReplicaAggregateRankFiveStrictRouteIncoming
    G sites hsite q hcard y
  have hrelated (w : ↑Incoming) :
      LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard w.1 y :=
    (mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
      G sites hsite q hcard y w.1).mp w.2
  let route (w : ↑Incoming) :
      ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q w.1) := Classical.choose (hrelated w)
  have hroute (w : ↑Incoming) :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard w.1 (route w) = y :=
    Classical.choose_spec (hrelated w)
  have htransfer (w : ↑Incoming) :
      ∃ e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z),
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
            G sites hsite q z e =
          lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
            G sites hsite q w.1 (route w) := by
    have hw :=
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_spatialWitness
        G sites hsite q hcard w.1 (route w)
    rw [hroute w, ← hzd] at hw
    exact
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness
        G sites hsite q hcard z d _ hw
  let encode (w : ↑Incoming) :
      ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z) := Classical.choose (htransfer w)
  have hencode (w : ↑Incoming) :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q z (encode w) =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q w.1 (route w) :=
    Classical.choose_spec (htransfer w)
  have hinjective : Function.Injective encode := by
    intro w v henc
    apply Subtype.ext
    apply
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_spatialSlot_eq_of_target_eq
        G sites hsite q hcard w.1 v.1 (route w) (route v)
    · rw [← hencode w, ← hencode v, henc]
    · exact (hroute w).trans (hroute v).symm
  have hcardFiber : Fintype.card ↑Incoming ≤
      Fintype.card
        ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z) :=
    Fintype.card_le_of_injective encode hinjective
  simpa only [Fintype.card_coe] using hcardFiber


theorem LPReplicaAggregateRankFiveStrictRouteWeight_sum_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    ∑ y : LPReplicaAggregateDecoratedTarget G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y = 1 := by
  classical
  let C :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z
  let f : ↑C -> LPReplicaAggregateDecoratedTarget G sites q :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
      G sites hsite q hcard z
  let R : Finset (LPReplicaAggregateDecoratedTarget G sites q) :=
    Finset.univ.image f
  have hf : Function.Injective f :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_injective
      G sites hsite q hcard z
  have hrelated (y : LPReplicaAggregateDecoratedTarget G sites q) :
      LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y ↔ y ∈ R := by
    simp only [LPReplicaAggregateRankFiveStrictRouteRelated, R,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, rfl⟩
    · rintro ⟨d, hd⟩
      exact ⟨d, hd⟩
  have hcardR : R.card = C.card := by
    change (Finset.univ.image f).card = C.card
    rw [Finset.card_image_iff.mpr]
    · simp
    · exact fun _ _ _ _ h => hf h
  have hpos : 0 < C.card :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_pos
      G sites hsite q hcard z
  calc
    (∑ y : LPReplicaAggregateDecoratedTarget G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y) =
        ∑ _y ∈ R, (C.card : Real)⁻¹ := by
      change ∑ y, (if
        LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y then (C.card : Real)⁻¹ else 0) = _
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          hrelated]
      · intro y _
        rfl
    _ = (R.card : Real) * (C.card : Real)⁻¹ := by simp
    _ = (C.card : Real) * (C.card : Real)⁻¹ := by rw [hcardR]
    _ = 1 := by
      exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hpos))


theorem LPReplicaAggregateRankFiveStrictRouteWeight_sum_source
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y) =
      ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 1 y).card : Real) +
        ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 2 y).card : Real) / 2 := by
  classical
  have hpoint
      (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
      LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y =
        (if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 1 y then 1 else 0) +
          (if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 2 y then (2 : Real)⁻¹ else 0) := by
    have hdegree :=
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two
        G sites hsite q hcard z
    rcases hdegree with hdegree | hdegree
    · by_cases hrelated : LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y
      · simp [LPReplicaAggregateRankFiveStrictRouteWeight,
          LPReplicaAggregateRankFiveStrictRouteIncomingDegree,
          hrelated, hdegree]
      · simp [LPReplicaAggregateRankFiveStrictRouteWeight,
          LPReplicaAggregateRankFiveStrictRouteIncomingDegree,
          hrelated, hdegree]
    · by_cases hrelated : LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y
      · simp [LPReplicaAggregateRankFiveStrictRouteWeight,
          LPReplicaAggregateRankFiveStrictRouteIncomingDegree,
          hrelated, hdegree]
      · simp [LPReplicaAggregateRankFiveStrictRouteWeight,
          LPReplicaAggregateRankFiveStrictRouteIncomingDegree,
          hrelated, hdegree]
  calc
    (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y) =
        ∑ z,
          ((if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 1 y then 1 else 0) +
            (if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
                G sites hsite q hcard 2 y then (2 : Real)⁻¹ else 0)) := by
      apply Finset.sum_congr rfl
      intro z _
      exact hpoint z
    _ = (∑ z, if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 1 y then (1 : Real) else 0) +
        ∑ z, if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 2 y then (2 : Real)⁻¹ else 0 :=
      Finset.sum_add_distrib
    _ = ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 1 y).card : Real) +
        ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 2 y).card : Real) / 2 := by
      simp [div_eq_mul_inv]


end
end StatMech.Ising
