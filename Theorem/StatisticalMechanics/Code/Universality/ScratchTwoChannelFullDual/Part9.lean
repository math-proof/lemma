/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part10
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_openSub_twoChannelFullOuter_eq_induce {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.openSub (rlc_twoChannelFullOuterGraph n)
        (rlc_twoChannelFullOuterConfig gamma gamma' omega) =
      openSubgraphInduce 2
        (rlc_dualReflectConfig
          (rlc_twoChannelFullAmbientConfig gamma gamma' omega))
        (rlc_twoChannelFullOuterBox n) := by
  ext x y
  simp only [FK.openSub_adj, openSubgraphInduce_adj, openSubgraph_adj]
  rfl

end
end StatMech.Universality
