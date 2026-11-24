module
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part6
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.Part4
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def LPReplicaAggregateRankFiveStrictRouteRerouteGraph
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    SimpleGraph (LPReplicaAggregateDecoratedTarget G sites q) :=
  SimpleGraph.fromRel fun y w =>
    w = lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y ∨
      ∃ z, LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y ∧
        LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z w


end
end StatMech.Ising
