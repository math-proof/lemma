/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaProfilePartialReflects
    (G : SimpleGraph V) (sites : I -> V)
    (m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop :=
  ∃ p, p <= m ∧ lpReplicaPartialReflectProfile G sites m p = n


end
end StatMech.Ising
