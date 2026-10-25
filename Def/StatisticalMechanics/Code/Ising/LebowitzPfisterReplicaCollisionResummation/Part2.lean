/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaReflectCopyEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m ≃
      StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) where
  toFun c := ⟨lpReplicaCurrentEdgeReflect G sites c.1,
    ⟨c.2.val, by
      change c.2.val < m (lpReplicaCurrentEdgeReflect G sites
        (lpReplicaCurrentEdgeReflect G sites c.1))
      rw [lpReplicaCurrentEdgeReflect_involutive]
      exact c.2.isLt⟩⟩
  invFun c := ⟨lpReplicaCurrentEdgeReflect G sites c.1,
    ⟨c.2.val, by
      exact c.2.isLt⟩⟩
  left_inv := by
    rintro ⟨e, k⟩
    let he := lpReplicaCurrentEdgeReflect_involutive G sites e
    apply Sigma.ext he
    exact (Fin.heq_ext_iff (congrArg m he)).2 rfl
  right_inv := by
    rintro ⟨e, k⟩
    let he := lpReplicaCurrentEdgeReflect_involutive G sites e
    apply Sigma.ext he
    exact (Fin.heq_ext_iff (congrArg
      (fun x => m (lpReplicaCurrentEdgeReflect G sites x)) he)).2 rfl

end
end StatMech.Ising
