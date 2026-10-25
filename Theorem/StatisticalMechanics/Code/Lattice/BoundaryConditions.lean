/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.Lattice.BoundaryConditions
open scoped BigOperators


set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Lattice

namespace BoundaryCondition

theorem free_ne_wired : (free ≠ wired) := by decide

theorem free_ne_periodic : (free ≠ periodic) := by decide

theorem wired_ne_periodic : (wired ≠ periodic) := by decide

end BoundaryCondition
end Lattice
end StatMech
