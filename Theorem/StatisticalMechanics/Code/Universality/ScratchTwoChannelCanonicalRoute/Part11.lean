/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelCanonicalRoute_mem {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    rlc_twoChannelCanonicalRoute eta ∈
      rlc_twoChannelSuccessfulSubconfigs eta := by
  exact Finset.min'_mem _ _

theorem rlc_twoChannelCanonicalRoute_open_subset {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    rlc_twoChannelOpenEdgeSet (rlc_twoChannelCanonicalRoute eta).1 ⊆
      rlc_twoChannelOpenEdgeSet eta.1 := by
  have hmem := rlc_twoChannelCanonicalRoute_mem eta
  simpa [rlc_twoChannelSuccessfulSubconfigs] using hmem


end
end StatMech.Universality
