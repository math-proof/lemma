/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate
        G sites q) := by
  intro z w h
  rcases z with ⟨i, j, b, z, hz⟩
  rcases w with ⟨i', j', b', w, hw⟩
  simp only [LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate]
    at h
  cases h
  rfl


theorem lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ≠ a.1 ∧
      lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ≠
        a.2.1 := by
  classical
  let a := z.toAggregate G sites q
  have hij : z.1 ≠ z.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hunmarked :=
    LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
      G sites hsite hij q hcard z.2.2.2.1 z.2.2.2.2
  exact ⟨
    (lpReplicaAggregateDecoratedSourceSelectedSeam_ne_left_of_unmarkedSaturated
      G sites hsite q a hunmarked),
    (lpReplicaAggregateDecoratedSourceSelectedSeam_ne_right_of_unmarkedSaturated
      G sites hsite q a hunmarked)⟩


theorem lpReplicaOffdiag_rankFive_handled_union_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    z ∈ lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q ∨
      z ∈ lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive
        G sites i j q := by
  classical
  by_cases hz : z ∈ lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
      G sites i j q
  · exact Or.inl hz
  · exact Or.inr (by
      simp only [lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive,
        Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hz)


theorem lpReplicaOffdiag_rankFive_card_handled_add_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
        G sites i j q).card +
      (lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive
        G sites i j q).card =
      Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive,
    Finset.union_eq_left.mpr (Finset.subset_univ _), Nat.add_comm] using
    (Finset.card_sdiff_add_card
      (s := (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)))
      (t := lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
        G sites i j q))


theorem card_lpReplicaAggregateDecoratedSource_rankFive_eq_handled_add_unmarked
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaAggregateDecoratedSource G sites q) =
      Fintype.card
          (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) +
        Fintype.card
          (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) := by
  classical
  rw [card_lpReplicaAggregateDecoratedSource,
    card_lpReplicaAggregateLowOrResolvableHighSourceRankFive,
    card_lpReplicaAggregateUnmarkedSaturatedSourceRankFive,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ↓reduceIte]
    exact (lpReplicaOffdiag_rankFive_card_handled_add_unmarkedSaturated
      G sites i j q).symm


theorem lpReplicaOffdiag_rankFive_handled_disjoint_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Disjoint
      (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q)
      (lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive G sites i j q) := by
  classical
  simpa only [lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive] using
    (Finset.disjoint_sdiff
      (s := lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
        G sites i j q)
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q))))

end
end StatMech.Ising
