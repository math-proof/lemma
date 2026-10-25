/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part9
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

open StatMech.Sharpness


def lpReplicaCollisionFiberMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Real :=
  ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m},
    weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) *
      weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites)
          (lpReplicaReflectedResidual G sites m K.1))


end
end StatMech.Ising
