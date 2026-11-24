module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
public import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
public import Def.StatisticalMechanics.Code.Walls.wcddefectbridge
open scoped BigOperators
open Finset
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Wcd

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc


@[simp] theorem wcd_siteToVtx_apply (f : Site 2) : wcd_siteToVtx f = (f 0, f 1) := rfl

end Wcd
end StatMech
