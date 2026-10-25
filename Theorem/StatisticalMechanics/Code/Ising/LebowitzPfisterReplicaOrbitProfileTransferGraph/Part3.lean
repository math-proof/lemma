/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part3


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiag_source_target_transferComponent_eq
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    lpReplicaOffdiagDecoratedSourceTransferComponent G sites i j q z =
      lpReplicaOffdiagDecoratedTargetTransferComponent G sites i j q y := by
  exact lpReplicaCommonOrbitTransferGraph_component_eq G sites q
    (lpReplicaOffdiagDecoratedSourceOrbitProfile G sites i j q z)
    (lpReplicaOffdiagDecoratedTargetOrbitProfile G sites i j q y)


end
end StatMech.Ising
