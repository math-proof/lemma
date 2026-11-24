module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Theorem.StatisticalMechanics.Code.Walls.jc_toprowrun
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc_RunLengths (K : Set (Site 2)) (c : Site 2) : Set ℕ :=
  {n | ∀ j : ℕ, j ≤ n → jc_shiftX c (j : ℤ) ∈ K}


end Walls
end StatMech
