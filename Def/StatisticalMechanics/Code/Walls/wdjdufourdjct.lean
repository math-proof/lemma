module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
public import Structure.StatisticalMechanics.Code.Walls.wdjdufourdjct
open Finset Set SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Walls


attribute [instance] wdj_Hypermap.finD wdj_Hypermap.decD

namespace wdj_Hypermap

variable (M : wdj_Hypermap)


def φ : Equiv.Perm M.D := M.α₁⁻¹ * M.α₀⁻¹

end wdj_Hypermap
end Lattice
end StatMech
