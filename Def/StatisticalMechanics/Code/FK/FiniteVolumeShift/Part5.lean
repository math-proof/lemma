/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Abbrev.StatisticalMechanics.Code.FK.FiniteVolumeShift
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


noncomputable def fvs_transEquiv (d m : ℕ) (v : Site d) :
    boxVerts d m ≃ fvs_transBoxVerts d m v where
  toFun := fun x => ⟨(x : Site d) + v, by
    show ((x : Site d) + v - v) ∈ box d m
    rw [add_sub_cancel_right]; exact x.2⟩
  invFun := fun y => ⟨(y : Site d) - v, y.2⟩
  left_inv := by intro x; apply Subtype.ext; simp
  right_inv := by intro y; apply Subtype.ext; simp

end FK
end StatMech
