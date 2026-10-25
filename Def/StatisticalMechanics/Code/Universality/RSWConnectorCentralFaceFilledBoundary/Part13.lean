/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part16
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_connectorCentralFaceGoodBoundaryGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    SimpleGraph (Site 2) where
  Adj f g :=
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g ∧
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g
  symm := by
    constructor
    rintro f g ⟨hfg, hgood⟩
    exact ⟨hfg.symm,
      (rlc_reflectedEdgeCarrierGeometry_comm gamma gamma' f g).1 hgood⟩
  loopless := ⟨fun f hff => hff.1.ne rfl⟩

end
end StatMech.Universality
