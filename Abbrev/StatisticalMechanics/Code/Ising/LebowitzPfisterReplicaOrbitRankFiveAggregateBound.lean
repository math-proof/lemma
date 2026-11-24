module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.Part4
public import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateBound
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateBound.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

abbrev LPReplicaAggregateSourceCrossTraceFiber
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :=
  {z : LPReplicaAggregateDecoratedSource G sites q //
    lpReplicaAggregateDecoratedSourceCrossTrace G sites q z = u}

end
end StatMech.Ising
