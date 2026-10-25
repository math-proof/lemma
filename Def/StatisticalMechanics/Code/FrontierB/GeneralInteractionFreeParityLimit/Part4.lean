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
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit.Part3
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

noncomputable def interactionBoxTransportedEdges (d : Nat) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n))) :
    Finset (Sym2 (interactionBoxVertices d m)) :=
  sym2FinsetMap (interactionBoxVertexIncl d hnm) E

end StatMech.FrontierB
