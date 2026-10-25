/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitTagReconstruction
open Finset


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaTaggedOrigin_collisionProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaCollisionProfile G sites
        (lpReplicaTaggedOriginProfile G sites m tag false)
        (lpReplicaTaggedOriginProfile G sites m tag true) = m := by
  funext e
  unfold lpReplicaCollisionProfile lpReplicaTaggedOriginProfile
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [lpReplicaCurrentEdgeReflect_involutive]
  unfold lpReplicaTaggedRowProfile
  rw [lpReplicaRowCopies_true_eq_compl_false,
    profileFlux_compl]
  exact Nat.add_sub_cancel'
    (profileFlux_le (lpReplicaCurrentGraph G sites) m
      (lpReplicaRowCopies G sites m tag false) e)


theorem lpReplicaTaggedOrigin_left_le
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaTaggedOriginProfile G sites m tag false <= m := by
  intro e
  exact profileFlux_le (lpReplicaCurrentGraph G sites) m
    (lpReplicaRowCopies G sites m tag false) e


end
end StatMech.Ising
