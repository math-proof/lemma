/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Def.StatisticalMechanics.Code.Lattice.DartNext.Part2
open SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem mkDart_tail (p g : Site 2) (hg : unitWt g = 1) :
    (mkDart p g hg).tail = p := rfl

@[simp] theorem mkDart_head (p g : Site 2) (hg : unitWt g = 1) :
    (mkDart p g hg).head = p + g := rfl

@[simp] theorem mkDart_dir (p g : Site 2) (hg : unitWt g = 1) :
    (mkDart p g hg).dir = g := by
  rw [Dart.dir_def, mkDart_head, mkDart_tail]; abel


end Lattice
end StatMech
