/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part18
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFaithfulFaceSeparateWiring_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma' ≤
      rlc_twoChannelFaithfulFaceMergedWiring gamma gamma' := by
  intro C D hCD
  rw [rlc_twoChannelFaithfulFaceSeparateWiring,
    SimpleGraph.sup_adj, Lattice.boundaryCliqueGraph_adj,
    Lattice.boundaryCliqueGraph_adj] at hCD
  rw [rlc_twoChannelFaithfulFaceMergedWiring,
    Lattice.boundaryCliqueGraph_adj]
  rcases hCD with hright | hleft
  · exact ⟨hright.1, Or.inl hright.2.1, Or.inl hright.2.2⟩
  · exact ⟨hleft.1, Or.inr hleft.2.1, Or.inr hleft.2.2⟩


end
end StatMech.Universality
