/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.ConnectiveBounds


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


@[simp] lemma zd_mem_sawWalks {d n : ℕ} {w : Fin n → ZdStep d} :
    w ∈ zdSAWWalks d n ↔ ZdIsSAW w := by simp [zdSAWWalks]

@[simp] lemma zd_mem_nbWalks {d n : ℕ} {w : Fin n → ZdStep d} :
    w ∈ zdNBWalks d n ↔ ZdIsNB w := by simp [zdNBWalks]


lemma zdStepVec_reverse {d : ℕ} (s : ZdStep d) :
    zdStepVec (zdReverse s) = - zdStepVec s := by
  funext j; unfold zdStepVec zdReverse
  by_cases hj : j = s.1
  · simp only [hj]; cases s.2 <;> simp
  · simp [hj]


lemma zdPos_succ {d n : ℕ} (w : Fin n → ZdStep d) (k : ℕ) :
    zdPos w (k + 1) = zdPos w k + zdStepN w k := by
  unfold zdPos; rw [Finset.sum_range_succ]


lemma zd_card_step (d : ℕ) : Fintype.card (ZdStep d) = 2 * d := by
  simp only [ZdStep, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring


lemma zd_card_ne (d : ℕ) (t : ZdStep d) :
    (Finset.univ.filter (fun s : ZdStep d => s ≠ t)).card = 2 * d - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ t),
    Finset.card_univ, zd_card_step]


end StatMech.Universality
