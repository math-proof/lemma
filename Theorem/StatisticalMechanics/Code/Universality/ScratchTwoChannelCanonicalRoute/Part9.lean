/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_mem_twoChannelOpenEdgeSet_iff {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    e ∈ rlc_twoChannelOpenEdgeSet omega ↔ omega e = true := by
  simp [rlc_twoChannelOpenEdgeSet]


end
end StatMech.Universality
