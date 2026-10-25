/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part3


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagDecoratedSourcesInTransferComponent
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z =>
    lpReplicaOffdiagDecoratedSourceTransferComponent G sites i j q z = c


noncomputable def lpReplicaOffdiagBalancedOutputsInTransferComponent
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagBalancedOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetTransferComponent G sites i j q y = c


noncomputable def lpReplicaOffdiagBalancedRelevantTransferComponents
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset
      (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent := by
  classical
  exact ((Finset.univ : Finset
      (LPReplicaOffdiagDecoratedSource G sites i j q)).image
        (lpReplicaOffdiagDecoratedSourceTransferComponent G sites i j q)) ∪
    (lpReplicaOffdiagBalancedOutputs G sites i j q).image
      (lpReplicaOffdiagDecoratedTargetTransferComponent G sites i j q)

end
end StatMech.Ising
