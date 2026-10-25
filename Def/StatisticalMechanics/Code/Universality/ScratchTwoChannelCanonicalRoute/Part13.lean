/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part14
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcBookFaithfulRetainedAnchorIncidence {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  RlcBookFaithfulTracePair gamma gamma' ∧
    ∀ (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))),
      rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' →
        ∃ L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho,
          RlcCentralFaceRetainedAnchorTraceIncidence L.boundary


end
end StatMech.Universality
