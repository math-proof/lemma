module
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.Part4
public import Theorem.StatisticalMechanics.Code.Foundations.FiniteBidegreeHall
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFivePairedHall.lean -/
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

noncomputable instance instFintypeLPReplicaAggregateDecoratedTargetBase
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaAggregateDecoratedTargetBase G sites q) := by
  unfold LPReplicaAggregateDecoratedTargetBase
  infer_instance


end
end StatMech.Ising
