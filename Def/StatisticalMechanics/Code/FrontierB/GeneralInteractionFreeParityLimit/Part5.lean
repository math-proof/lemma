module
public import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit.Part4
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Ising Lattice

noncomputable def interactionEdgeVertexSupport {d : Nat}
    (F : Finset (Sym2 (Site d))) : Finset (Site d) :=
  F.biUnion Sym2.toFinset

end StatMech.FrontierB
