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
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

def interactionBoxLiftEdge {d n : Nat} (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (e : ↑F) : Sym2 (interactionBoxVertices d n) :=
  e.1.attachWith (fun x hx => mem_interactionBoxVertices.mpr
    (hFbox e.1 e.2 x hx))

end StatMech.FrontierB
