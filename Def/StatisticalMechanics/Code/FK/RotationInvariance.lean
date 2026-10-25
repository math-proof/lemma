/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part6
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.show false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


def rot_permEquiv (d : ℕ) (π : Equiv.Perm (Fin d)) : Site d ≃ Site d where
  toFun := fun x i => x (π.symm i)
  invFun := fun x i => x (π i)
  left_inv := by intro x; funext i; simp
  right_inv := by intro x; funext i; simp

end FK
end StatMech
