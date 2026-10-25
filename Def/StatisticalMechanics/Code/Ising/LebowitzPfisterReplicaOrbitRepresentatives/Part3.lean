/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCardinality.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRepresentatives.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaCurrentEdgeOrbitStrictReps
    (G : SimpleGraph V) (sites : I -> V) :
    Finset (lpReplicaCurrentGraph G sites).edgeFinset := by
  classical
  exact (lpReplicaCurrentEdgeOrbitReps G sites).filter fun e =>
    e ≠ lpReplicaCurrentEdgeReflect G sites e


noncomputable def lpReplicaCurrentEdgeOrbitFixed
    (G : SimpleGraph V) (sites : I -> V) :
    Finset (lpReplicaCurrentGraph G sites).edgeFinset := by
  classical
  exact Finset.univ.filter fun e =>
    e = lpReplicaCurrentEdgeReflect G sites e

end
end StatMech.Ising
