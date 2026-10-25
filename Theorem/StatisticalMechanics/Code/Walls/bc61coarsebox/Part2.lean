/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc60upperlines.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc61coarsebox.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc61_mem_boxAround_zero {L : ℕ} {x : Site 2} :
    x ∈ bc61_boxAround 2 L 0 ↔ x ∈ box 2 L := by
  rw [bc61_mem_boxAround]; simp


theorem bc61_pt_outside_boxAround {L : ℕ} {k h : ℤ} (hk : (L : ℤ) < k) :
    bc57_pt k h ∉ bc61_boxAround 2 L 0 := by
  rw [bc61_mem_boxAround_zero, mem_box]
  simp only [not_forall, not_le]
  refine ⟨0, ?_⟩
  rw [bc57_pt_fst]; omega


theorem bc61_upperLines_rightArm_reach {L : ℕ} {h : ℤ} (hh : 1 ≤ h) (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
      (bc57_pt ((L : ℤ) + 1) h) (bc57_pt ((L : ℤ) + 1 + (j : ℤ)) h) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt ((L : ℤ) + 1) h)
  | succ i ih =>
    have hcol : (L : ℤ) < (L : ℤ) + 1 + (i : ℤ) := by omega
    have hcol1 : (L : ℤ) < (L : ℤ) + 1 + (i : ℤ) + 1 := by omega
    have hstep : Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
        (bc57_pt ((L : ℤ) + 1 + (i : ℤ)) h) (bc57_pt ((L : ℤ) + 1 + (i : ℤ) + 1) h) :=
      bc61_cut_adj_connected (bc57_pt_adj _ h) (bc60_open _ hh)
        (bc61_pt_outside_boxAround hcol) (bc61_pt_outside_boxAround hcol1)
    have hcast : ((L : ℤ) + 1 + ((i + 1 : ℕ) : ℤ)) = (L : ℤ) + 1 + (i : ℤ) + 1 := by
      push_cast; ring
    rw [hcast]; exact ih.trans hstep


theorem bc61_upperLines_rightArm_infinite {L : ℕ} {h : ℤ} (hh : 1 ≤ h) :
    (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
      (bc57_pt ((L : ℤ) + 1) h)).Infinite := by
  rw [cluster_infinite_iff]
  intro j
  refine ⟨bc57_pt ((L : ℤ) + 1 + ((L : ℤ) + 1 + (j : ℤ))) h, ?_, ?_⟩
  · rw [mem_box]; simp only [not_forall, not_le]; refine ⟨0, ?_⟩
    rw [bc57_pt_fst]
    have : (L : ℤ) + 1 + ((L : ℤ) + 1 + (j : ℤ)) ≥ (j : ℤ) + 1 := by omega
    omega
  · have := bc61_upperLines_rightArm_reach (L := L) hh ((L : ℤ) + 1 + (j : ℤ)).toNat
    have hcast : (((L : ℤ) + 1 + (j : ℤ)).toNat : ℤ) = (L : ℤ) + 1 + (j : ℤ) := by
      rw [Int.toNat_of_nonneg]; positivity
    rwa [hcast] at this


theorem bc61_upperLines_arm_disconnected {L : ℕ} {h h' : ℤ} (hne : h ≠ h') :
    ¬ Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
      (bc57_pt ((L : ℤ) + 1) h) (bc57_pt ((L : ℤ) + 1) h') := by
  intro hconn
  have hω : Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) h) (bc57_pt ((L : ℤ) + 1) h') :=
    bc61_connected_of_cut hconn
  have hht : (bc57_pt ((L : ℤ) + 1) h') 1 = h :=
    bc60_height_invariant (by rw [bc57_pt_snd]) hω
  rw [bc57_pt_snd] at hht
  exact hne hht.symm


theorem bc61_upperLines_arm_boxAdjacent {L : ℕ} {h : ℤ} (hh : 1 ≤ h) (hhL : h ≤ (L : ℤ)) :
    ∃ b ∈ bc61_boxAround 2 L 0, (openSubgraph 2 bc60_upperLines).Adj b (bc57_pt ((L : ℤ) + 1) h) := by
  refine ⟨bc57_pt (L : ℤ) h, ?_, ?_⟩
  · rw [bc61_mem_boxAround_zero, mem_box]; intro i; fin_cases i
    · change ((bc57_pt (L : ℤ) h) 0).natAbs ≤ L; rw [bc57_pt_fst]; simp
    · change ((bc57_pt (L : ℤ) h) 1).natAbs ≤ L; rw [bc57_pt_snd]; omega
  · exact ⟨bc57_pt_adj (L : ℤ) h, bc60_open (L : ℤ) hh⟩


theorem bc61_wholeBox_severs_upperLines {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) := by
  refine ⟨bc57_pt ((L : ℤ) + 1) 1, bc57_pt ((L : ℤ) + 1) 2, bc57_pt ((L : ℤ) + 1) 3,
    bc61_upperLines_arm_boxAdjacent (by norm_num) (by exact_mod_cast (by omega : (1:ℤ) ≤ L)),
    bc61_upperLines_arm_boxAdjacent (by norm_num) (by exact_mod_cast (by omega : (2:ℤ) ≤ L)),
    bc61_upperLines_arm_boxAdjacent (by norm_num) (by exact_mod_cast (by omega : (3:ℤ) ≤ L)),
    ⟨bc61_upperLines_rightArm_infinite (by norm_num),
     bc61_upperLines_rightArm_infinite (by norm_num),
     bc61_upperLines_rightArm_infinite (by norm_num)⟩,
    ⟨?_, ?_, ?_⟩⟩
  · exact bc61_upperLines_arm_disconnected (by norm_num)
  · exact bc61_upperLines_arm_disconnected (by norm_num)
  · exact bc61_upperLines_arm_disconnected (by norm_num)


theorem bc61_singleSite_fails_upperLines {G : Finset (Sym2 (Site 2))} {a a' : Site 2}
    (ha : a 1 ≤ 1) (ha' : a' 1 ≤ 1)
    (hinf : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite)
    (hinf' : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite) :
    Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a' :=
  bc60_arms_connected ha ha' hinf hinf'


theorem bc61_contrast_upperLines {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
    (∀ (G : Finset (Sym2 (Site 2))) (a a' : Site 2), a 1 ≤ 1 → a' 1 ≤ 1 →
      (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite →
      (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite →
      Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a') :=
  ⟨bc61_wholeBox_severs_upperLines hL,
   fun _ _ _ ha ha' hinf hinf' => bc61_singleSite_fails_upperLines ha ha' hinf hinf'⟩


end StatMech.Walls
