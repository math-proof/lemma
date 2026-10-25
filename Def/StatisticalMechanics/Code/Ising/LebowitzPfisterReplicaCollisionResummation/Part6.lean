/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaCollisionCopyEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaCollisionCopy G sites a b ≃
      StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b) :=
  Equiv.sigmaCongrRight (fun _ => finSumFinEquiv)

end
end StatMech.Ising
