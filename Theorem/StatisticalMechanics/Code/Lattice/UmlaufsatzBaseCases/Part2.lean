/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzBaseCases
open SimpleGraph Function


namespace StatMech

namespace Lattice

open Real in


theorem umBase_turnAngle_mem (K : Set (Site 2)) (e : Dart) :
    turnAngle K e = Real.pi / 2 ∨ turnAngle K e = 0 ∨ turnAngle K e = -(Real.pi / 2) := by
  unfold turnAngle
  rcases turnZ_mem K e with h | h | h <;> rw [h]
  · left; push_cast; ring
  · right; left; push_cast; ring
  · right; right; push_cast; ring

open Real in


theorem umBase_abs_turnAngle_le (K : Set (Site 2)) (e : Dart) :
    |turnAngle K e| ≤ Real.pi / 2 := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rcases umBase_turnAngle_mem K e with h | h | h <;> rw [h]
  · rw [abs_of_nonneg hpi]
  · simpa using hpi
  · rw [abs_neg, abs_of_nonneg hpi]


end Lattice
end StatMech
