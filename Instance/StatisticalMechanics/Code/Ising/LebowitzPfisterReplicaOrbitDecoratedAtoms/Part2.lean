/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable instance instFintypeLPReplicaCollisionSplitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaCollisionSplitLabel G sites m K) := by
  classical
  unfold LPReplicaCollisionSplitLabel
  infer_instance

end
end StatMech.Ising
