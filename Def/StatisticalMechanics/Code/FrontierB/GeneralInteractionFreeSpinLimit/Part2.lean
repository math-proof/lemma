/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit
open Filter Topology Set
open scoped BigOperators
open Finset


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Sharpness StatMech.Lattice


noncomputable def interactionBoxSpinSupport (d n : Nat)
    (A : Finset (Site d)) : Finset (interactionBoxVertices d n) :=
  Finset.univ.filter fun x => x.1 ∈ A

end StatMech.FrontierB
