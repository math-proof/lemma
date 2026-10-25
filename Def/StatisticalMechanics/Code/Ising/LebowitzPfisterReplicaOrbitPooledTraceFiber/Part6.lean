/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaAggregateDecoratedInjection
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop :=
  ∃ move : LPReplicaAggregateDecoratedSource G sites q ->
      LPReplicaAggregateDecoratedTarget G sites q,
    Function.Injective move

end
end StatMech.Ising
