module
public import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
public import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
public import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part29
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

@[simp] theorem rlc_twoChannelFullVariableTargetEdge_inner_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    (rlc_twoChannelFullVariableTargetEdge_inner target).1.map Subtype.val =
      target.1 :=
  Classical.choose_spec
    (rlc_twoChannelFullVariableTargetEdge_inner_exists target)


end
end StatMech.Universality
