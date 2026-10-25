/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaAggregateDecoratedSourceCrossTrace
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOffdiagDecoratedSourceCrossTrace G sites z.1 z.2.1 q z.2.2.2


noncomputable def lpReplicaAggregateDecoratedTargetCrossTrace
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOffdiagDecoratedTargetCrossTrace
    G sites y.2.1 y.2.2.1 q (Sum.inl y.2.2.2)


def LPReplicaAggregateCrossToggleRelated
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  lpReplicaAggregateDecoratedTargetCrossTrace G sites q y =
    lpReplicaAggregateDecoratedSourceCrossTrace G sites q z


noncomputable def lpReplicaAggregateCrossToggleNeighbors
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaAggregateCrossToggleRelated G sites q z y


noncomputable def LPReplicaAggregateCrossToggleHall
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaAggregateDecoratedSource G sites q),
    S.card <= (S.biUnion
      (lpReplicaAggregateCrossToggleNeighbors G sites q)).card


end
end StatMech.Ising
