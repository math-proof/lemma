/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part4
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


def fkTI_signFlipEquiv (d : ℕ) (j : Fin d) : Site d ≃ Site d where
  toFun := fun x i => if i = j then -(x i) else x i
  invFun := fun x i => if i = j then -(x i) else x i
  left_inv := by intro x; funext i; by_cases h : i = j <;> simp [h]
  right_inv := by intro x; funext i; by_cases h : i = j <;> simp [h]


def fkTI_signFlip (d : ℕ) (j : Fin d) : BoxSym d where
  τ := fkTI_signFlipEquiv d j
  adj := by
    intro x y
    simp only [hypercubicLattice_adj, fkTI_signFlipEquiv, Equiv.coe_fn_mk]
    have hcoord : ∀ i : Fin d,
        ((if i = j then -(x i) else x i) - (if i = j then -(y i) else y i)).natAbs
          = (x i - y i).natAbs := by
      intro i
      by_cases hh : i = j
      · rw [if_pos hh, if_pos hh, show -(x i) - -(y i) = -(x i - y i) by ring, Int.natAbs_neg]
      · rw [if_neg hh, if_neg hh]
    rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
  box_mem := by
    intro n x
    simp only [mem_box, fkTI_signFlipEquiv, Equiv.coe_fn_mk]
    have hcoord : ∀ i : Fin d, (if i = j then -(x i) else x i).natAbs = (x i).natAbs := by
      intro i
      by_cases hh : i = j
      · rw [if_pos hh, Int.natAbs_neg]
      · rw [if_neg hh]
    constructor
    · intro h i; rw [← hcoord i]; exact h i
    · intro h i; rw [hcoord i]; exact h i


end FK
end StatMech
