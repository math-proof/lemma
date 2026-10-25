/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rot90Fun_iterate_four_eq (x : Site 2) : rot90Fun^[4] x = x := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  exact rot90Fun_four x


theorem rot90Fun_iterate_mod (n : ℕ) (x : Site 2) :
    rot90Fun^[n] x = rot90Fun^[n % 4] x := by
  conv_lhs => rw [← Nat.mod_add_div n 4]
  rw [Function.iterate_add_apply, Function.iterate_mul]
  congr 1
  exact Function.iterate_fixed (rot90Fun_iterate_four_eq x) (n / 4)


end Lattice
end StatMech
