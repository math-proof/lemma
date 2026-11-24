module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
public import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
public import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_connectorCentralFaceExteriorComponent_infinite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (rlc_connectorCentralFaceExteriorComponent gamma gamma' rho).supp.Infinite :=
  (Classical.choose_spec (unique_infinite_component (by norm_num)
    (rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho))).1


end
end StatMech.Universality
