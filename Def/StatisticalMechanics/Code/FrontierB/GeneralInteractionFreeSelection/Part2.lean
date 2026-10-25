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
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSelection
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

noncomputable def interactionBoxPullbackPattern {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) {A : Type*}
    (a : ↑F → A) :
    ↑(interactionBoxLiftedEdgeIndices F hFbox hFdiag) → A :=
  a ∘ (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm

end StatMech.FrontierB
