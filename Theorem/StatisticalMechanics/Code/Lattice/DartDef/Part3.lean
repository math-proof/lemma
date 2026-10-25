/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.DartDef
open SimpleGraph


namespace StatMech

namespace Lattice

namespace Dart

@[simp] theorem rev_tail (d : Dart) : d.rev.tail = d.head := rfl

@[simp] theorem rev_head (d : Dart) : d.rev.head = d.tail := rfl


@[simp] theorem rev_rev (d : Dart) : d.rev.rev = d := rfl


end Dart
end Lattice
end StatMech
