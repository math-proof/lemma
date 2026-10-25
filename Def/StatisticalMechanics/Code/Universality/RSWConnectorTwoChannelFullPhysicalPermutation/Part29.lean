/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part28
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (B : Set (RlcConnectorVertex n)) (f g : Site 2) : Prop :=
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_reflectedPathEdges gamma'.1) ∨
    ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      target.1.map Subtype.val =
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
        ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g


end
end StatMech.Universality
