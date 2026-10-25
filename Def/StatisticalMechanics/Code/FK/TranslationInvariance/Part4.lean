/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Structure.StatisticalMechanics.Code.FK.TranslationInvariance
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


def BoxSym.lift (S : BoxSym d) (n : ℕ) : boxVerts d n ≃ boxVerts d n where
  toFun := fun x => ⟨S.τ x.val, (S.box_mem n x.val).mpr x.property⟩
  invFun := fun x => ⟨S.τ.symm x.val, by
    rw [← S.box_mem n (S.τ.symm x.val), Equiv.apply_symm_apply]; exact x.property⟩
  left_inv := by intro x; apply Subtype.ext; simp
  right_inv := by intro x; apply Subtype.ext; simp

end FK
end StatMech
