/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part2


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaOffdiagDecoratedSourceOrbitProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaCommonOrbitProfile G sites q :=
  ⟨z.1.1.1, z.1.1.2⟩


def lpReplicaOffdiagDecoratedTargetOrbitProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaCommonOrbitProfile G sites q :=
  match y with
  | Sum.inl z => ⟨z.1.1.1, z.1.1.2⟩
  | Sum.inr z => ⟨z.1.1.1, z.1.1.2⟩


def lpReplicaOffdiagDecoratedSourceTransferComponent
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent :=
  (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk
    (lpReplicaOffdiagDecoratedSourceOrbitProfile G sites i j q z)


def lpReplicaOffdiagDecoratedTargetTransferComponent
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent :=
  (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk
    (lpReplicaOffdiagDecoratedTargetOrbitProfile G sites i j q y)


end
end StatMech.Ising
