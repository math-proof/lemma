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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part19
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalFilledBoundarySegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      ∀ e ∈ a.edges,
        ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
          target.1.1.map Subtype.val = e.map rlc_dualReflect


noncomputable def rlc_twoChannelFullPhysicalGoodBoundaryGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : SimpleGraph (Site 2) where
  Adj f g := (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g ∧
    ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      target.1.1.map Subtype.val =
        s(rlc_dualReflect f, rlc_dualReflect g)
  symm := by
    constructor
    rintro f g ⟨hfg, target, htarget⟩
    refine ⟨hfg.symm, target, ?_⟩
    simpa [Sym2.eq_swap] using htarget
  loopless := ⟨fun f hff => hff.1.ne rfl⟩

end
end StatMech.Universality
