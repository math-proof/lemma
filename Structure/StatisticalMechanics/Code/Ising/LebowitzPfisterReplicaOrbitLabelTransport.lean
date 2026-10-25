/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaProfileOrbitSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  allocation : forall e :
    ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Finset (Fin (q e.1))
  selectedRep : forall e :
    ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Finset (Fin (q e.1))
  selectedReflect : forall e :
    ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Finset (Fin (q e.1))
  selectedRep_subset : forall e, selectedRep e ⊆ allocation e
  selectedReflect_subset : forall e,
    selectedReflect e ⊆ Finset.univ \ allocation e

end
end StatMech.Ising
