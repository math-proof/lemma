/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part47
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFaithfulForcedDualEdgeProb_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp1 : p < 1) (q : Real)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFaithfulForcedDualEdgeProb gamma gamma' p q omega =
      FK.indexedBcProb (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
  unfold rlc_twoChannelFaithfulForcedDualEdgeProb FK.indexedBcProb
  rw [rlc_twoChannelFaithful_pfdDualWeight_eq_indexed,
    rlc_twoChannelFaithfulForcedDualEdgeZ_eq_indexed]
  apply mul_div_mul_left
  exact pow_ne_zero _ (by linarith)


end
end StatMech.Universality
