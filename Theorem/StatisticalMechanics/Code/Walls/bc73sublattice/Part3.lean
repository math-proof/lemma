/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc72quotient.Part3
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc73sublattice.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc73_far_of_sameResidue {L : ℕ} {y y' : Site d}
    (hres : bc73_resVec L y = bc73_resVec L y') (hne : y ≠ y') :
    ∃ i, 2 * L < ((y - y') i).natAbs := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ y' i := by
    by_contra h; simp only [not_exists, not_not] at h; exact hne (funext h)
  refine ⟨i, ?_⟩
  
  have hposZ : (0 : ℤ) < 2 * L + 1 := by positivity
  have hresi : (y i % (2 * L + 1 : ℤ)).toNat = (y' i % (2 * L + 1 : ℤ)).toNat := by
    have := congrArg (fun f => (f i).val) hres
    simpa [bc73_resVec] using this
  have hnn1 : 0 ≤ y i % (2 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
  have hnn2 : 0 ≤ y' i % (2 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
  have hemodeq : y i % (2 * L + 1 : ℤ) = y' i % (2 * L + 1 : ℤ) := by
    have : (y i % (2 * L + 1 : ℤ)).toNat = (y' i % (2 * L + 1 : ℤ)).toNat := hresi
    omega
  have hdvd : (2 * L + 1 : ℤ) ∣ (y - y') i := by
    rw [Pi.sub_apply]
    have hmodeq : (y i - y' i) % (2 * L + 1 : ℤ) = 0 := by
      rw [Int.sub_emod, hemodeq, sub_self, Int.zero_emod]
    exact Int.dvd_of_emod_eq_zero hmodeq
  have hnz : (y - y') i ≠ 0 := by rw [Pi.sub_apply]; exact sub_ne_zero.mpr hi
  have hdvdabs : (2 * L + 1 : ℤ) ∣ |(y - y') i| := (dvd_abs _ _).mpr hdvd
  have hge : (2 * L + 1 : ℤ) ≤ |(y - y') i| := Int.le_of_dvd (abs_pos.mpr hnz) hdvdabs
  have hge' : (2 * L + 1 : ℤ) ≤ ((y - y') i).natAbs := by rwa [Int.abs_eq_natAbs] at hge
  have : (2 * L + 1 : ℕ) ≤ ((y - y') i).natAbs := by exact_mod_cast hge'
  omega


theorem bc73_sameResidue_boxes_disjoint {L : ℕ} {y y' : Site d}
    (hres : bc73_resVec L y = bc73_resVec L y') (hne : y ≠ y') :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') :=
  bc64_boxAround_disjoint_of_far (bc73_far_of_sameResidue hres hne)


end StatMech.Walls
