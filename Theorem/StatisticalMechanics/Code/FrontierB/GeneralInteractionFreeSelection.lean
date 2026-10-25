/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSelection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit.Part6
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentFiniteMarginal.Part2
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSelection
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

@[simp] theorem interactionBoxEdgeIncl_liftIndex {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) (e : ↑F) :
    interactionBoxEdgeIncl d n
        (interactionBoxLiftIndexEmbedding F hFbox hFdiag e) = e.1 := by
  exact interactionBoxLiftEdge_map_val F hFbox e

theorem restrictCurrent_extendInteractionBoxCurrent_lift {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag)
    (m : EdgeCurrent (interactionBoxGraph d n)) :
    restrictCurrent F (extendInteractionBoxCurrent d n m) =
      fun e => restrictCurrent
        (interactionBoxLiftedEdgeIndices F hFbox hFdiag) m
          (interactionBoxLiftIndexEquiv F hFbox hFdiag e) := by
  funext e
  change extendInteractionBoxCurrent d n m e.1 =
    m (interactionBoxLiftIndexEquiv F hFbox hFdiag e).1
  have heq : (interactionBoxLiftIndexEquiv F hFbox hFdiag e).1 =
      interactionBoxLiftIndexEmbedding F hFbox hFdiag e := rfl
  rw [heq, ← interactionBoxEdgeIncl_liftIndex F hFbox hFdiag e]
  exact extendInteractionBoxCurrent_included d n m
    (interactionBoxLiftIndexEmbedding F hFbox hFdiag e)

end StatMech.FrontierB
