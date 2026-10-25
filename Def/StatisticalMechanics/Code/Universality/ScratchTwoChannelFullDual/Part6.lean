/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def rlc_twoChannelFullExteriorSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Set (Site 2) :=
  {z | ∃ hz : z ∈ (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ,
    ((hypercubicLattice 2).induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ).connectedComponentMk
        ⟨z, hz⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega}


def rlc_twoChannelFullFilledReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Set (Site 2) :=
  (rlc_twoChannelFullExteriorSet gamma gamma' omega)ᶜ

end
end StatMech.Universality
