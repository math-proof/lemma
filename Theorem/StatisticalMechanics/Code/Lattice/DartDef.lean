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
open SimpleGraph


namespace StatMech

namespace Lattice

theorem rot90Fun_rot90Fun (x : Site 2) : rot90Fun (rot90Fun x) = -x := by
  funext i; fin_cases i <;> simp [rot90Fun]


theorem rot90Fun_four (x : Site 2) :
    rot90Fun (rot90Fun (rot90Fun (rot90Fun x))) = x := by
  rw [rot90Fun_rot90Fun, ← rot90Fun_rot90Fun]
  funext i; fin_cases i <;> simp [rot90Fun]


theorem rot90Fun_iterate_four : rot90Fun ∘ rot90Fun ∘ rot90Fun ∘ rot90Fun = id := by
  funext x; exact rot90Fun_four x


end Lattice
end StatMech
