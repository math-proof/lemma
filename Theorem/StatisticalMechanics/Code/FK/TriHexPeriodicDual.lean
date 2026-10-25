/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Abbrev.StatisticalMechanics.Code.FK.TriHexPeriodicDual
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

theorem triangularStep_injective : Function.Injective triangularStep := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangularStep]

theorem triangularStep_add_ne_zero (i j : Fin 3) :
    triangularStep i + triangularStep j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp [triangularStep, funext_iff]


end PeriodicPlanar
end FK
end StatMech
