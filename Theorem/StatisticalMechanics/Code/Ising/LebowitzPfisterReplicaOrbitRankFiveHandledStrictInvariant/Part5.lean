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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part4


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_subset_component
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
        G sites hsite q hcard y ⊆
      LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y := by
  classical
  intro w hw
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood,
    Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rcases hw with rfl | hwflip | ⟨z, hzin, hzw⟩
  · exact SimpleGraph.Reachable.refl _
  · rw [hwflip]
    apply SimpleGraph.Adj.reachable
    rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
      SimpleGraph.fromRel_adj]
    refine ⟨lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne
      G sites q y |>.symm, Or.inl ?_⟩
    exact Or.inl rfl
  · have hzy : LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y :=
      (mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
        G sites hsite q hcard y z).mp hzin
    by_cases hyw : y = w
    · subst w
      exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
        SimpleGraph.fromRel_adj]
      exact ⟨hyw, Or.inl (Or.inr ⟨z, hzy, hzw⟩)⟩


theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponent_eq_of_reachable
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hyw : (LPReplicaAggregateRankFiveStrictRouteRerouteGraph
      G sites hsite q hcard).Reachable y w) :
    LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y =
      LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard w := by
  classical
  ext t
  simp only [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun hyt => hyw.symm.trans hyt
  · exact fun hwt => hyw.trans hwt


theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_not_reachable
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hyw : ¬ (LPReplicaAggregateRankFiveStrictRouteRerouteGraph
      G sites hsite q hcard).Reachable y w) :
    Disjoint
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y)
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard w) := by
  classical
  rw [Finset.disjoint_left]
  intro t hyt hwt
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter] at hyt hwt
  exact hyw (hyt.2.trans hwt.2.symm)


theorem
    lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_selectedSeam_ne
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hseam : y.2.1 ≠ w.2.1) :
    Disjoint
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y)
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard w) := by
  apply lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_not_reachable
    G sites hsite q hcard y w
  intro hyw
  exact hseam
    (lpReplicaAggregateRankFiveStrictRouteRerouteGraph_reachable_selectedSeam_eq
      G sites hsite q hcard hyw)


theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponent_flip_mem
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y t : LPReplicaAggregateDecoratedTarget G sites q)
    (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y) :
    lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q t ∈
      LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y := by
  classical
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter] at ht ⊢
  refine ⟨Finset.mem_univ _, ht.2.trans ?_⟩
  apply SimpleGraph.Adj.reachable
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
    SimpleGraph.fromRel_adj]
  refine ⟨lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne
      G sites q t |>.symm, Or.inl ?_⟩
  exact Or.inl rfl


theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponent_related_mem
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y t w : LPReplicaAggregateDecoratedTarget G sites q)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y)
    (hzt : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z t)
    (hzw : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z w) :
    w ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y := by
  classical
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter] at ht ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases htw : t = w
  · subst w
    exact ht.2
  · apply ht.2.trans
    apply SimpleGraph.Adj.reachable
    rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
      SimpleGraph.fromRel_adj]
    exact ⟨htw, Or.inl (Or.inr ⟨z, hzt, hzw⟩)⟩


end
end StatMech.Ising
