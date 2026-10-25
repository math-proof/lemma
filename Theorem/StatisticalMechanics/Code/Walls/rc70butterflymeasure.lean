/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc69doubledmeasure.Part2
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Def.StatisticalMechanics.Code.Walls.rc70butterflymeasure
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc70_wt_half (U : Finset (Fin n ⊕ Fin n)) :
    rc70_wt n (1/2) U = (1/2) ^ (2 * n) := by
  unfold rc70_wt
  have hcard : U.card ≤ 2 * n := by
    have := Finset.card_le_univ U
    simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using this
  have : (1 : ℚ) - 1/2 = 1/2 := by norm_num
  rw [this, ← pow_add]
  congr 1
  omega


theorem rc70_measure_half (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    rc70_measure n (1/2) Fam = Fam.card * (1/2) ^ (2 * n) := by
  unfold rc70_measure
  rw [Finset.sum_congr rfl (fun U _ => rc70_wt_half U)]
  rw [Finset.sum_const, nsmul_eq_mul]


theorem rc70_measure_half_invariant (i : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    rc70_measure n (1/2) (StatMech.doubleCompress i Fam) = rc70_measure n (1/2) Fam := by
  rw [rc70_measure_half, rc70_measure_half, StatMech.doubleCompress_card]


set_option maxRecDepth 4000 in


theorem rc70_witness_compressed :
    StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})
      = {{Sum.inr 0}} := by decide

set_option maxRecDepth 4000 in


theorem rc70_witness_start :
    StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅} = {∅} := by decide


theorem rc70_measure_increases_at_three_quarters :
    rc70_measure 2 (3/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}) = 1/256
    ∧ rc70_measure 2 (3/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) = 3/256 := by
  constructor
  · rw [rc70_witness_start, rc70_measure, Finset.sum_singleton, rc70_wt]
    norm_num
  · rw [rc70_witness_compressed, rc70_measure, Finset.sum_singleton, rc70_wt, Finset.card_singleton]
    norm_num


theorem rc70_measure_decreases_at_one_quarter :
    rc70_measure 2 (1/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}) = 81/256
    ∧ rc70_measure 2 (1/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) = 27/256 := by
  constructor
  · rw [rc70_witness_start, rc70_measure, Finset.sum_singleton, rc70_wt]
    norm_num
  · rw [rc70_witness_compressed, rc70_measure, Finset.sum_singleton, rc70_wt, Finset.card_singleton]
    norm_num


theorem rc70_weighted_measure_not_monotone :
    (rc70_measure 2 (3/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})
        < rc70_measure 2 (3/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})))
    ∧ (rc70_measure 2 (1/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}))
        < rc70_measure 2 (1/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) := by
  refine ⟨?_, ?_⟩
  · rw [rc70_measure_increases_at_three_quarters.1, rc70_measure_increases_at_three_quarters.2]
    norm_num
  · rw [rc70_measure_decreases_at_one_quarter.1, rc70_measure_decreases_at_one_quarter.2]
    norm_num


end StatMech.Walls
