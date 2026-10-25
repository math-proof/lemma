/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaOffdiagCrossTraceFiberInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  move : LPReplicaOffdiagDecoratedSource G sites i j q ->
    LPReplicaOffdiagDecoratedTarget G sites i j q
  output_mem : forall z,
    move z ∈ lpReplicaOffdiagBalancedOutputs G sites i j q
  trace_eq : forall z,
    lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q (move z) =
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z
  injective_on_trace : forall z w,
    lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w ->
    move z = move w -> z = w


end
end StatMech.Ising
