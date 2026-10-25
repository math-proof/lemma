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
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

def interactionBoxLiftIndexEmbedding {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    ↑F ↪ (interactionBoxGraph d n).edgeFinset where
  toFun e := ⟨interactionBoxLiftEdge F hFbox e,
    interactionBoxLiftedEdges_subset_edgeFinset F hFbox hFdiag (by
      unfold interactionBoxLiftedEdges
      exact Finset.mem_map.mpr ⟨e, Finset.mem_univ e, rfl⟩)⟩
  inj' e f hef := by
    apply Subtype.ext
    exact congrArg Subtype.val
      ((interactionBoxLiftEdgeEmbedding F hFbox).injective
        (congrArg Subtype.val hef))

noncomputable def interactionBoxLiftedEdgeIndices {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    Finset (interactionBoxGraph d n).edgeFinset :=
  Finset.univ.map (interactionBoxLiftIndexEmbedding F hFbox hFdiag)

noncomputable def interactionBoxLiftIndexEquiv {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    ↑F ≃ ↑(interactionBoxLiftedEdgeIndices F hFbox hFdiag) :=
  Equiv.ofBijective
    (fun e => ⟨interactionBoxLiftIndexEmbedding F hFbox hFdiag e, by
      simp [interactionBoxLiftedEdgeIndices]⟩)
    ⟨fun _ _ h => (interactionBoxLiftIndexEmbedding F hFbox hFdiag).injective
        (congrArg Subtype.val h),
      fun i => by
        have hi := i.2
        change i.1 ∈ Finset.univ.map
          (interactionBoxLiftIndexEmbedding F hFbox hFdiag) at hi
        rw [Finset.mem_map] at hi
        obtain ⟨e, he, hei⟩ := hi
        refine ⟨e, ?_⟩
        apply Subtype.ext
        exact hei⟩

end StatMech.FrontierB
