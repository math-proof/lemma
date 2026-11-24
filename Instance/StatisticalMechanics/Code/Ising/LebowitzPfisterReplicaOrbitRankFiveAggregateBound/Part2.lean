module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.Part4
public import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateBound
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

noncomputable instance instFintypeLPReplicaAggregateSourceCrossTraceFiber
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Fintype (LPReplicaAggregateSourceCrossTraceFiber G sites q u) :=
  Fintype.ofFinite _


end
end StatMech.Ising
