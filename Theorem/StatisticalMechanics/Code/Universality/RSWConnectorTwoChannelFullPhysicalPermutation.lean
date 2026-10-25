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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_twoChannelFullPhysicalSourceEdge_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma') :
    (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val =
      rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) :=
  target.2.some.2

theorem rlc_twoChannelFullPhysicalSourceEdge_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective
      (rlc_twoChannelFullPhysicalSourceEdge
        (gamma := gamma) (gamma' := gamma')) := by
  intro target target' hsource
  apply Subtype.ext
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  apply rlc_pimsEdgeEquiv.injective
  rw [← rlc_twoChannelFullPhysicalSourceEdge_map target,
    ← rlc_twoChannelFullPhysicalSourceEdge_map target', hsource]

end
end StatMech.Universality
