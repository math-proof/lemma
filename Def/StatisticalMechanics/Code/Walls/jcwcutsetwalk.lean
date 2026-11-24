module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
public import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
public import Theorem.StatisticalMechanics.Code.Walls.ceosimplecycle
open Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


def jcw_shiftFace : Site 2 → Prop := fun f => f = ![0, 1]


end Walls
end StatMech
