/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCardinality.Part2
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRepresentatives
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaCurrentEdgeRank
    (G : SimpleGraph V) (sites : I -> V) :
    (lpReplicaCurrentGraph G sites).edgeFinset ->
      Fin (Fintype.card (lpReplicaCurrentGraph G sites).edgeFinset) :=
  Fintype.equivFin _

end
end StatMech.Ising
