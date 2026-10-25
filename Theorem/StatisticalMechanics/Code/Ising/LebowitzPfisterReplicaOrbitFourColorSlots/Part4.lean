/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaProfileCopyEquivOrbitCoord_fst
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaProfileCopyEquivOrbitCoord G sites m c).1 =
      lpReplicaCurrentEdgeOrbitCoordEquiv G sites c.1 := by
  rfl


@[simp] theorem lpReplicaProfileCopyEquivOrbitCoord_snd_val
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaProfileCopyEquivOrbitCoord G sites m c).2.1 = c.2.1 := by
  rcases c with ⟨e, k⟩
  have castVal (a b : Nat) (h : a = b) (x : Fin a) :
      (Equiv.cast (congrArg Fin h) x).1 = x.1 := by
    subst b
    rfl
  let E := lpReplicaCurrentEdgeOrbitCoordEquiv G sites
  change (Equiv.cast (congrArg Fin
    (congrArg m (E.symm_apply_apply e).symm)) k).1 = k.1
  exact castVal _ _ (congrArg m (E.symm_apply_apply e).symm) k


@[simp] theorem lpReplicaProfileCopyEquivOrbitCoord_edge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm
        (lpReplicaProfileCopyEquivOrbitCoord G sites m c).1 = c.1 := by
  exact (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm_apply_apply c.1


end
end StatMech.Ising
