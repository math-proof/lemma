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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

structure RlcCentralFaceLowestFilledAxisGap {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) where
  height : Int
  height_lower : (gamma.1.1 : Site 2) 1 ≤ height
  height_upper : height < (gamma'.1.2.1 : Site 2) 1
  axis_inside : ![0, height] ∈
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  axis_outside : ![0, height + 1] ∉
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  axis_below_inside : ∀ s : Int,
    (gamma.1.1 : Site 2) 1 ≤ s → s ≤ height →
      ![0, s] ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  boundary : ((![0, height], ![0, height + 1]) ∈ edgeBoundary 2
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))


end
end StatMech.Universality
