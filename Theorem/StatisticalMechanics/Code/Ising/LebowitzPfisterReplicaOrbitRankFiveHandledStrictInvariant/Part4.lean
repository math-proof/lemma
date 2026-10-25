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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part3


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateRankFiveStrictRouteRerouteGraph_adj_selectedSeam_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    {y w : LPReplicaAggregateDecoratedTarget G sites q}
    (hyw : (LPReplicaAggregateRankFiveStrictRouteRerouteGraph
      G sites hsite q hcard).Adj y w) :
    y.2.1 = w.2.1 := by
  classical
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
    SimpleGraph.fromRel_adj] at hyw
  rcases hyw.2 with hyw | hwy
  · rcases hyw with hflip | ⟨z, hzy, hzw⟩
    · rw [hflip]
      rfl
    · exact lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq
        G sites hsite q hcard z y w hzy hzw
  · rcases hwy with hflip | ⟨z, hzw, hzy⟩
    · rw [hflip]
      rfl
    · exact (lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq
        G sites hsite q hcard z w y hzw hzy).symm


theorem lpReplicaAggregateRankFiveStrictRouteRerouteGraph_reachable_selectedSeam_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    {y w : LPReplicaAggregateDecoratedTarget G sites q}
    (hyw : (LPReplicaAggregateRankFiveStrictRouteRerouteGraph
      G sites hsite q hcard).Reachable y w) :
    y.2.1 = w.2.1 := by
  have hreach := (SimpleGraph.reachable_iff_reflTransGen y w).mp hyw
  exact Relation.ReflTransGen.trans_induction_on hreach
    (fun _ => rfl)
    (fun hadj =>
      lpReplicaAggregateRankFiveStrictRouteRerouteGraph_adj_selectedSeam_eq
        G sites hsite q hcard hadj)
    (fun _ _ hleft hright => Eq.trans hleft hright)


end
end StatMech.Ising
