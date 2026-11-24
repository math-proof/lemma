module
public import Mathlib
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.TwoDim.Crossings.Part3
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace TwoDim

open StatMech.Lattice

variable {a b : ℤ}


@[simp]
theorem mem_horizontalCrossingEvent {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ horizontalCrossingEvent a b ↔ HorizontalCrossing ω a b := Iff.rfl


end TwoDim
end StatMech
