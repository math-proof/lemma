/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part14
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

@[simp] theorem rlc_twoChannelFullSourceEdge_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    (rlc_twoChannelFullSourceEdge target).1.map Subtype.val =
      rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
  exact Classical.choose_spec (rlc_twoChannelFullSourceEdge_exists target)

theorem rlc_twoChannelFullSourceEdge_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective
      (rlc_twoChannelFullSourceEdge (gamma := gamma) (gamma' := gamma')) := by
  intro target target' hsource
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  apply rlc_pimsEdgeEquiv.injective
  rw [← rlc_twoChannelFullSourceEdge_map target,
    ← rlc_twoChannelFullSourceEdge_map target', hsource]

end
end StatMech.Universality
