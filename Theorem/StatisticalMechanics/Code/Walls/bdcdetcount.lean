/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfctfinitecount.Part4
import Theorem.StatisticalMechanics.Code.Walls.bsgspantreegn
import Def.StatisticalMechanics.Code.Walls.bdcdetcount
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

theorem bdc_allOpen_indexAllOpen (L : ℕ) (j : Site 2) :
    bgf2_IndexAllOpen bdc_allOpenCfg L j := by
  intro x y hx hy hadj; rfl


theorem bdc_idx_ptL0 (L : ℕ) : bgn_idx L (bc57_pt (L : ℤ) 0) = 0 := by
  funext i
  fin_cases i
  · show ((bc57_pt (L : ℤ) 0) 0 + (L : ℤ)) / (2 * (L : ℤ) + 1) = (0 : Site 2) 0
    rw [bc57_pt_fst]; exact Int.ediv_eq_zero_of_lt (by positivity) (by omega)
  · show ((bc57_pt (L : ℤ) 0) 1 + (L : ℤ)) / (2 * (L : ℤ) + 1) = (0 : Site 2) 1
    rw [bc57_pt_snd]; exact Int.ediv_eq_zero_of_lt (by positivity) (by omega)


theorem bdc_idx_ptL10 (L : ℕ) : bgn_idx L (bc57_pt ((L : ℤ) + 1) 0) = bc57_pt 1 0 := by
  funext i
  fin_cases i
  · show ((bc57_pt ((L : ℤ) + 1) 0) 0 + (L : ℤ)) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 0
    rw [bc57_pt_fst, bc57_pt_fst]
    have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
    have hrw : ((L : ℤ) + 1) + (L : ℤ) = (0 : ℤ) + 1 * (2 * (L : ℤ) + 1) := by ring
    rw [hrw, Int.add_mul_ediv_right _ _ hb, Int.ediv_eq_zero_of_lt (by positivity) (by omega)]
    norm_num
  · show ((bc57_pt ((L : ℤ) + 1) 0) 1 + (L : ℤ)) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 1
    rw [bc57_pt_snd, bc57_pt_snd]
    exact Int.ediv_eq_zero_of_lt (by positivity) (by omega)


theorem bdc_q_ptL0 (L : ℕ) : bgf2_q bdc_allOpenCfg L (bc57_pt (L : ℤ) 0) = 0 := by
  unfold bgf2_q
  rw [bdc_idx_ptL0, if_pos (bdc_allOpen_indexAllOpen L 0), bgf2_centre_zero]


theorem bdc_q_ptL10 (L : ℕ) :
    bgf2_q bdc_allOpenCfg L (bc57_pt ((L : ℤ) + 1) 0) = bc57_pt (2 * (L : ℤ) + 1) 0 := by
  unfold bgf2_q
  rw [bdc_idx_ptL10, if_pos (bdc_allOpen_indexAllOpen L (bc57_pt 1 0))]
  funext i; fin_cases i
  · show bgf2_centre L (bc57_pt 1 0) 0 = (bc57_pt (2 * (L : ℤ) + 1) 0) 0
    simp [bgf2_centre, bc57_pt_fst]
  · show bgf2_centre L (bc57_pt 1 0) 1 = (bc57_pt (2 * (L : ℤ) + 1) 0) 1
    simp [bgf2_centre, bc57_pt_snd]


theorem bdc_Gf_centre_edge (L : ℕ) :
    (bgf2_Gf bdc_allOpenCfg L).Adj 0 (bc57_pt (2 * (L : ℤ) + 1) 0) := by
  refine ⟨?_, bc57_pt (L : ℤ) 0, bc57_pt ((L : ℤ) + 1) 0, bdc_q_ptL0 L, bdc_q_ptL10 L, ?_⟩
  · intro hc
    have := congrFun hc 0
    rw [bc57_pt_fst] at this; simp only [Pi.zero_apply] at this; omega
  · rw [openSubgraph_adj]
    refine ⟨?_, rfl⟩
    rw [hypercubicLattice_adj, Fin.sum_univ_two, bc57_pt_fst, bc57_pt_fst, bc57_pt_snd, bc57_pt_snd]
    omega


theorem bdc_Gf_not_le_lattice {L : ℕ} (hL : 1 ≤ L) :
    ¬ (bgf2_Gf bdc_allOpenCfg L ≤ hypercubicLattice 2) := by
  intro hle
  have hadj := hle (bdc_Gf_centre_edge L)
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  simp only [Pi.zero_apply, bc57_pt_fst, bc57_pt_snd] at hadj
  omega


theorem bdc_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω L R h


end StatMech.Walls
