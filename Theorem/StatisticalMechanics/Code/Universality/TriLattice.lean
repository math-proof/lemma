/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.TriLattice


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


@[simp] lemma tri_mem_sawWalks {n : ℕ} {w : Fin n → TriStep} :
    w ∈ triSAWWalks n ↔ TriIsSAW w := by simp [triSAWWalks]

@[simp] lemma tri_mem_nbWalks {n : ℕ} {w : Fin n → TriStep} :
    w ∈ triNBWalks n ↔ TriIsNB w := by simp [triNBWalks]


lemma triStepVec_reverse (s : TriStep) :
    triStepVec (triReverse s) = - triStepVec s := by
  funext j
  fin_cases s <;> fin_cases j <;> rfl


lemma triReverse_reverse (s : TriStep) : triReverse (triReverse s) = s := by
  fin_cases s <;> rfl


lemma triReverse_ne (s : TriStep) : triReverse s ≠ s := by
  fin_cases s <;> decide


lemma triPos_succ {n : ℕ} (w : Fin n → TriStep) (k : ℕ) :
    triPos w (k + 1) = triPos w k + triStepN w k := by
  unfold triPos; rw [Finset.sum_range_succ]


lemma tri_card_step : Fintype.card TriStep = 6 := by
  simp [TriStep]


lemma tri_card_ne (t : TriStep) :
    (Finset.univ.filter (fun s : TriStep => s ≠ t)).card = 5 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ t),
    Finset.card_univ, tri_card_step]


end StatMech.Universality
