/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_connectorCentralFaceFiniteGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (hypercubicLattice 2).Adj x.1 y.1 ∧
    s(x.1, y.1) ∈ rlc_connectorCentralFaceEdges gamma gamma'
  symm := by
    constructor
    rintro x y ⟨hxy, he⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using he⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

end
end StatMech.Universality
