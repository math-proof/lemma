/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
import Def.StatisticalMechanics.Code.Walls.bgnglobalcontract
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


@[simp] theorem bgn_Gn_adj (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (j k : Site d) :
    (bgn_Gn ω L).Adj j k ↔
      j ≠ k ∧ ∃ a b : Site d, bgn_idx L a = j ∧ bgn_idx L b = k ∧ (openSubgraph d ω).Adj a b :=
  Iff.rfl


theorem bgn_ediv_zero {L : ℕ} {a : ℤ} (h0 : 0 ≤ a) (hlt : a < 2 * (L : ℤ) + 1) :
    a / (2 * (L : ℤ) + 1) = 0 :=
  Int.ediv_eq_zero_of_lt h0 hlt


theorem bgn_idx_adversarySite (L : ℕ) (hL : 1 ≤ L) :
    bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) = bc57_pt 1 0 := by
  funext i
  fin_cases i
  · show (((bc57_pt ((L : ℤ) + 1) 1) 0) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 0
    rw [bc57_pt_fst, bc57_pt_fst]
    have : ((L : ℤ) + 1) + L = 2 * (L : ℤ) + 1 := by ring
    rw [this, Int.ediv_self (by positivity)]
  · show (((bc57_pt ((L : ℤ) + 1) 1) 1) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 1
    rw [bc57_pt_snd, bc57_pt_snd]
    exact bgn_ediv_zero (by positivity) (by omega)


theorem bgn_idx_trifCentre (L : ℕ) (hL : 1 ≤ L) :
    bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) = bc57_pt 1 0 := by
  funext i
  fin_cases i
  · show (((bc57_pt (2 * (L : ℤ) + 1) 0) 0) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 0
    rw [bc57_pt_fst, bc57_pt_fst]
    have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
    have hrw : (2 * (L : ℤ) + 1) + L = (L : ℤ) + 1 * (2 * (L : ℤ) + 1) := by ring
    rw [hrw, Int.add_mul_ediv_right _ _ hb, bgn_ediv_zero (by positivity) (by omega)]
    norm_num
  · show (((bc57_pt (2 * (L : ℤ) + 1) 0) 1) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 1
    rw [bc57_pt_snd, bc57_pt_snd]
    exact bgn_ediv_zero (by positivity) (by omega)


theorem bgn_idx_origin (L : ℕ) (hL : 1 ≤ L) :
    bgn_idx L (0 : Site 2) = bc57_pt 0 0 := by
  funext i
  fin_cases i
  · show (((0 : Site 2) 0) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 0 0) 0
    rw [bc57_pt_fst]
    simpa using bgn_ediv_zero (by positivity) (by omega)
  · show (((0 : Site 2) 1) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 0 0) 1
    rw [bc57_pt_snd]
    simpa using bgn_ediv_zero (by positivity) (by omega)


theorem bgn_ground_common (L : ℕ) (hL : 1 ≤ L) :
    bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) = bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) ∧
    bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) ≠ bgn_idx L (0 : Site 2) := by
  refine ⟨?_, ?_⟩
  · rw [bgn_idx_adversarySite L hL, bgn_idx_trifCentre L hL]
  · rw [bgn_idx_adversarySite L hL, bgn_idx_origin L hL]
    intro h
    have := congrFun h 0
    rw [bc57_pt_fst, bc57_pt_fst] at this
    exact one_ne_zero this


end StatMech.Walls
