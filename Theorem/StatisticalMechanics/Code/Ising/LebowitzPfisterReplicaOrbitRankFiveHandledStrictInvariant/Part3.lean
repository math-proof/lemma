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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part2


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y y' : LPReplicaAggregateDecoratedTarget G sites q)
    (hzy : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y)
    (hzy' : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y') :
    y.2.1 = y'.2.1 := by
  obtain ⟨d, rfl⟩ := hzy
  obtain ⟨e, rfl⟩ := hzy'
  simp


theorem lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_selectedSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y y' : LPReplicaAggregateDecoratedTarget G sites q)
    (hy' : y' ∈ LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
      G sites hsite q hcard y) :
    y'.2.1 = y.2.1 := by
  classical
  simp only [LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood,
    Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
  rcases hy' with rfl | hy'flip | ⟨z, hzy, hzy'⟩
  · rfl
  · rw [hy'flip]
    rfl
  · have hzyRelated : LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y :=
      (mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
        G sites hsite q hcard y z).mp hzy
    exact
      lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq
        G sites hsite q hcard z y' y hzy' hzyRelated


theorem lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_disjoint_of_selectedSeam_ne
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hseam : y.2.1 ≠ w.2.1) :
    Disjoint
      (LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
        G sites hsite q hcard y)
      (LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
        G sites hsite q hcard w) := by
  classical
  rw [Finset.disjoint_left]
  intro t hty htw
  apply hseam
  rw [
    ← lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_selectedSeam
      G sites hsite q hcard y t hty,
    ← lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_selectedSeam
      G sites hsite q hcard w t htw]


end
end StatMech.Ising
