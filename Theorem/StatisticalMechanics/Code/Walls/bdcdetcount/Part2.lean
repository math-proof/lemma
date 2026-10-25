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
import Def.StatisticalMechanics.Code.Walls.bdcdetcount.Part2
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

@[simp] theorem bdc_shiftCfg_edge (c : Site 2) (ω : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    bdc_shiftCfg c ω s(x, y) = ω s(x + c, y + c) := by
  unfold bdc_shiftCfg; rw [Sym2.map_mk]


theorem bdc_lat_shift (c x y : Site 2) :
    (hypercubicLattice 2).Adj (x + c) (y + c) ↔ (hypercubicLattice 2).Adj x y := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj]
  refine Iff.of_eq (congrArg (· = 1) ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.add_apply]; congr 1; ring


theorem bdc_openSub_shift (c : Site 2) (ω : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    (openSubgraph 2 (bdc_shiftCfg c ω)).Adj x y ↔ (openSubgraph 2 ω).Adj (x + c) (y + c) := by
  rw [openSubgraph_adj, openSubgraph_adj, bdc_shiftCfg_edge, bdc_lat_shift]


theorem bdc_bgn_idx_shift (L : ℕ) (j x : Site 2) :
    bgn_idx L (x + bgf2_centre L j) = bgn_idx L x + j := by
  funext i
  have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
  show ((x + bgf2_centre L j) i + (L : ℤ)) / (2 * (L : ℤ) + 1) = bgn_idx L x i + j i
  rw [Pi.add_apply]
  show (x i + bgf2_centre L j i + (L : ℤ)) / (2 * (L : ℤ) + 1)
      = (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) + j i
  have hc : bgf2_centre L j i = (2 * (L : ℤ) + 1) * j i := rfl
  rw [hc]
  have hrw : x i + (2 * (L : ℤ) + 1) * j i + (L : ℤ)
      = (x i + (L : ℤ)) + j i * (2 * (L : ℤ) + 1) := by ring
  rw [hrw, Int.add_mul_ediv_right _ _ hb]


theorem bdc_centre_add (L : ℕ) (a b : Site 2) :
    bgf2_centre L (a + b) = bgf2_centre L a + bgf2_centre L b := by
  funext i
  show (2 * (L : ℤ) + 1) * (a + b) i = (2 * (L : ℤ) + 1) * a i + (2 * (L : ℤ) + 1) * b i
  rw [Pi.add_apply]; ring


theorem bdc_indexAllOpen_shift (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j k : Site 2) :
    bgf2_IndexAllOpen (bdc_shiftCfg (bgf2_centre L j) ω) L k ↔ bgf2_IndexAllOpen ω L (k + j) := by
  set c := bgf2_centre L j with hc
  constructor
  · intro H x' y' hx' hy' hadj'
    have hxc : bgn_idx L (x' - c) = k := by
      have := bdc_bgn_idx_shift L j (x' - c)
      rw [sub_add_cancel] at this; rw [this] at hx'; exact add_right_cancel hx'
    have hyc : bgn_idx L (y' - c) = k := by
      have := bdc_bgn_idx_shift L j (y' - c)
      rw [sub_add_cancel] at this; rw [this] at hy'; exact add_right_cancel hy'
    have hadjc : (hypercubicLattice 2).Adj (x' - c) (y' - c) := by
      have hh := bdc_lat_shift c (x' - c) (y' - c)
      rw [sub_add_cancel, sub_add_cancel] at hh; exact hh.mp hadj'
    have := H (x' - c) (y' - c) hxc hyc hadjc
    rwa [bdc_shiftCfg_edge, sub_add_cancel, sub_add_cancel] at this
  · intro H x y hx hy hadj
    rw [bdc_shiftCfg_edge]
    refine H (x + c) (y + c) ?_ ?_ ?_
    · rw [bdc_bgn_idx_shift, hx]
    · rw [bdc_bgn_idx_shift, hy]
    · rwa [bdc_lat_shift]


theorem bdc_q_shift (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j x : Site 2) :
    bgf2_q (bdc_shiftCfg (bgf2_centre L j) ω) L x = bgf2_q ω L (x + bgf2_centre L j) - bgf2_centre L j := by
  set c := bgf2_centre L j with hc
  have key : bgn_idx L (x + c) = bgn_idx L x + j := bdc_bgn_idx_shift L j x
  unfold bgf2_q
  by_cases hP : bgf2_IndexAllOpen ω L (bgn_idx L (x + c))
  · have hPs : bgf2_IndexAllOpen (bdc_shiftCfg c ω) L (bgn_idx L x) := by
      rw [bdc_indexAllOpen_shift, ← key]; exact hP
    rw [if_pos hPs, if_pos hP, key, hc, bdc_centre_add]
    abel
  · have hPs : ¬ bgf2_IndexAllOpen (bdc_shiftCfg c ω) L (bgn_idx L x) := by
      rw [bdc_indexAllOpen_shift, ← key]; exact hP
    rw [if_neg hPs, if_neg hP]; abel


theorem bdc_Gf_shift_adj (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j u v : Site 2) :
    (bgf2_Gf (bdc_shiftCfg (bgf2_centre L j) ω) L).Adj u v ↔
      (bgf2_Gf ω L).Adj (u + bgf2_centre L j) (v + bgf2_centre L j) := by
  set c := bgf2_centre L j with hc
  rw [bgf2_Gf_adj, bgf2_Gf_adj]
  constructor
  · rintro ⟨huv, a, b, ha, hb, hab⟩
    refine ⟨fun h => huv (add_right_cancel h), a + c, b + c, ?_, ?_,
      (bdc_openSub_shift c ω a b).mp hab⟩
    · have := ha; rw [bdc_q_shift] at this; exact sub_eq_iff_eq_add.mp this
    · have := hb; rw [bdc_q_shift] at this; exact sub_eq_iff_eq_add.mp this
  · rintro ⟨huv, a', b', ha', hb', hab'⟩
    refine ⟨fun h => huv (by rw [h]), a' - c, b' - c, ?_, ?_, ?_⟩
    · rw [bdc_q_shift, sub_add_cancel, ha', add_sub_cancel_right]
    · rw [bdc_q_shift, sub_add_cancel, hb', add_sub_cancel_right]
    · rw [bdc_openSub_shift, sub_add_cancel, sub_add_cancel]; exact hab'


end StatMech.Walls
