/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCollisionSplitMultiplicity_eq_edgeProduct
    (G : SimpleGraph V) (sites : I -> V)
    (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaCollisionSplitMultiplicity G sites m K =
      ∏ e : (lpReplicaCurrentGraph G sites).edgeFinset,
        Nat.choose (m e) (K e) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  unfold lpReplicaCollisionSplitMultiplicity
  rw [<- Finset.prod_attach H.edgeFinset]
  apply Finset.prod_congr rfl
  intro e he
  simp only [ofEdgeFun]
  rw [dif_pos e.2, dif_pos e.2]


end
end StatMech.Ising
