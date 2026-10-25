/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit.Part2
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

def interactionBoxLiftEdgeEmbedding {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n) :
    ↑F ↪ Sym2 (interactionBoxVertices d n) where
  toFun := interactionBoxLiftEdge F hFbox
  inj' e f hef := by
    apply Subtype.ext
    have h := congrArg (Sym2.map Subtype.val) hef
    simpa using h

noncomputable def interactionBoxLiftedEdges {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n) :
    Finset (Sym2 (interactionBoxVertices d n)) :=
  Finset.univ.map (interactionBoxLiftEdgeEmbedding F hFbox)

end StatMech.FrontierB
