/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part5
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaCollisionLeftCopyEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) a ↪
      StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b) :=
  ({
    toFun := fun c => ⟨c.1, Sum.inl c.2⟩
    inj' := by
      rintro ⟨e, k⟩ ⟨f, l⟩ h
      cases h
      rfl
  } : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) a ↪
      LPReplicaCollisionCopy G sites a b).trans
    (lpReplicaCollisionCopyEquiv G sites a b).toEmbedding


def lpReplicaCollisionRightCopyEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) b ↪
      StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b) :=
  (lpReplicaReflectCopyEquiv G sites b).toEmbedding |>.trans
    (({
      toFun := fun c => ⟨c.1, Sum.inr c.2⟩
      inj' := by
        rintro ⟨e, k⟩ ⟨f, l⟩ h
        cases h
        rfl
    } : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites)
            (fun e => b (lpReplicaCurrentEdgeReflect G sites e)) ↪
        LPReplicaCollisionCopy G sites a b).trans
        (lpReplicaCollisionCopyEquiv G sites a b).toEmbedding)

end
end StatMech.Ising
