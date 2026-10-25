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
import Def.StatisticalMechanics.Code.Lattice.DartDef.Part2
open SimpleGraph


namespace StatMech

namespace Lattice

namespace Dart

@[simp] theorem dir_def (d : Dart) : d.dir = d.head - d.tail := rfl


@[simp] theorem dir_rev (d : Dart) : d.rev.dir = - d.dir := by
  simp only [dir, rev_tail, rev_head]; abel

end Dart
end Lattice
end StatMech
