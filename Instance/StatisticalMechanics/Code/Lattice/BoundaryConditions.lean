/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Inductive.StatisticalMechanics.Code.Lattice.BoundaryConditions

@[expose] public section

open scoped BigOperators


set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Lattice

namespace BoundaryCondition

instance : Inhabited BoundaryCondition := ⟨free⟩


end BoundaryCondition
end Lattice
end StatMech
