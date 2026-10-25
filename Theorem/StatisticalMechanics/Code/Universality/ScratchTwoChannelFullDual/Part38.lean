/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part46
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFaithfulForcedDualEdgeZ_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q =
      (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.indexedBcZ (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q := by
  unfold rlc_twoChannelFaithfulForcedDualEdgeZ FK.indexedBcZ
  simp_rw [rlc_twoChannelFaithful_pfdDualWeight_eq_indexed]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (rlc_twoChannelFaithfulDualEquiv gamma gamma')
    (fun eta => FK.indexedBcWeight
      (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q eta)


end
end StatMech.Universality
