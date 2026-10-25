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
import Structure.StatisticalMechanics.Code.Lattice.DartDef
open SimpleGraph


namespace StatMech

namespace Lattice

namespace Dart

@[ext] theorem ext {d e : Dart} (ht : d.tail = e.tail) (hh : d.head = e.head) :
    d = e := by
  cases d; cases e; cases ht; cases hh; rfl


end Dart
end Lattice
end StatMech
