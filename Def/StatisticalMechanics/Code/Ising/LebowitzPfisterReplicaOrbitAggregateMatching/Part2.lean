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
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaAggregatePooledSourceIntermediate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    LPReplicaAggregatePooledIntermediate G sites q := by
  let hij := lpReplicaAggregateDecoratedSource_indices_ne G sites q z
  cases lpReplicaOffdiagPooledSourceIntermediate
      G sites hsite hij q z.2.2.2 with
  | inl u => exact ⟨z.1, u⟩
  | inr u => exact ⟨z.2.1, u⟩


noncomputable def lpReplicaAggregatePooledTargetIntermediate
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaAggregatePooledIntermediate G sites q :=
  ⟨y.2.1, lpReplicaOffdiagPooledTargetLeftIntermediate
    G sites y.2.1 y.2.2.1 q y.2.2.2⟩


def LPReplicaAggregatePooledRelated
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  lpReplicaAggregatePooledTargetIntermediate G sites q y =
    lpReplicaAggregatePooledSourceIntermediate G sites hsite q z


noncomputable def lpReplicaAggregatePooledNeighbors
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaAggregatePooledRelated G sites hsite q z y


noncomputable def LPReplicaAggregatePooledHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaAggregateDecoratedSource G sites q),
    S.card <= (S.biUnion
      (lpReplicaAggregatePooledNeighbors G sites hsite q)).card


end
end StatMech.Ising
