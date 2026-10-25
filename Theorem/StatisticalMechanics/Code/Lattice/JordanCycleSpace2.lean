/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcx_faceCount_eq_nullity_add_one {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) : faceCount K = nullity K + 1 := rfl


theorem jcx_nullity_bot {V : Type*} [Finite V] [DecidableEq V] :
    nullity (⊥ : SimpleGraph V) = 0 :=
  nullity_eq_zero_of_isAcyclic (isAcyclic_bot)


theorem jcx_whb_bot_card :
    Nat.card (whb_faceRegion (⊥ : SimpleGraph (Site 2))).ConnectedComponent = 1 := by
  rw [jfc_whb_bot]
  have hreach : ∀ a b : Site 2, (hypercubicLattice 2).Reachable a b :=
    fun a b => pbs_reach_all a b
  have hsub : Subsingleton (hypercubicLattice 2).ConnectedComponent :=
    ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hreach a b))⟩
  haveI : Nonempty (hypercubicLattice 2).ConnectedComponent :=
    ⟨(hypercubicLattice 2).connectedComponentMk ![0, 0]⟩
  rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, inferInstance⟩


end Lattice
end StatMech
