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
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaAggregateSelectedSeamRelated
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z = y.2.1


noncomputable def lpReplicaAggregateSelectedSeamNeighbors
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaAggregateSelectedSeamRelated G sites hsite q z y


noncomputable def LPReplicaAggregateSelectedSeamHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaAggregateDecoratedSource G sites q),
    S.card <= (S.biUnion
      (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q)).card


def LPReplicaAggregateSelectedSeamCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop :=
  forall k : I,
    Fintype.card {z : LPReplicaAggregateDecoratedSource G sites q //
      lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z = k} <=
    Fintype.card {y : LPReplicaAggregateDecoratedTarget G sites q //
      y.2.1 = k}


end
end StatMech.Ising
