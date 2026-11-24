module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.jc_runnoup
public import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
public import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc2_FullyThick (K : Set (Site 2)) (c : Site 2) (len : ℤ) : Prop :=
  ∀ j : ℤ, 0 ≤ j → j ≤ len → jc2_downCell (c + ![j, 0]) ∈ K


end Walls
end StatMech
