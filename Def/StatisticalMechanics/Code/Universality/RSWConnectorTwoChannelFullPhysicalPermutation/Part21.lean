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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part20
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalBoundaryCarrierGeometry {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) : Prop :=
  ∃ target source :
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
    target.1.map Subtype.val =
        s(rlc_dualReflect f, rlc_dualReflect g) ∧
      source.1.map Subtype.val = sharedPrimalEdge f g


def RlcTwoChannelFullPhysicalTargetCarrierGeometry {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) : Prop :=
  ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
    target.1.map Subtype.val =
      s(rlc_dualReflect f, rlc_dualReflect g)


def RlcTwoChannelFullPhysicalSourceCarrierGeometry {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) : Prop :=
  ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
    source.1.map Subtype.val = sharedPrimalEdge f g


def RlcTwoChannelFullPhysicalTargetCarrierLocal {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) : Prop :=
  ∃ (hf : rlc_dualReflect f ∈ rect (-2 * n) (2 * n) (-n) n)
    (hg : rlc_dualReflect g ∈ rect (-2 * n) (2 * n) (-n) n),
    (rlc_connectorTwoChannelGraph gamma gamma').Adj
      ⟨rlc_dualReflect f, hf⟩ ⟨rlc_dualReflect g, hg⟩

end
end StatMech.Universality
