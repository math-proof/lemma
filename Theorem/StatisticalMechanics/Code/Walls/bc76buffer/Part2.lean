/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc75spanningtree.Part4
import Def.StatisticalMechanics.Code.Walls.bc76buffer.Part2
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


theorem bc76_yBuf_box_disjoint (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) := by
  refine bc64_boxAround_disjoint_of_farCoord 0 ?_
  have hcoord : ((0 : Site 2) - bc76_yBuf L) 0 = -(4 * (L : ℤ) + 1) := by
    simp only [Pi.sub_apply, bc76_yBuf]; rw [bc57_pt_fst]; simp
  rw [hcoord, Int.natAbs_neg]
  have hval : (4 * (L : ℤ) + 1).natAbs = 4 * L + 1 := by
    have : (4 * (L : ℤ) + 1) = ((4 * L + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.natAbs_natCast]
  omega


theorem bc76_collapse_zero {L : ℕ} {x : Site 2} (hx : x ∈ bc61_boxAround 2 L (0 : Site 2)) :
    bc76_twoBoxCollapse L x = 0 := by unfold bc76_twoBoxCollapse; rw [if_pos hx]


theorem bc76_collapse_buf {L : ℕ} {x : Site 2} (hx : x ∈ bc61_boxAround 2 L (bc76_yBuf L)) :
    bc76_twoBoxCollapse L x = bc76_yBuf L := by
  unfold bc76_twoBoxCollapse
  have hx0 : x ∉ bc61_boxAround 2 L (0 : Site 2) :=
    fun h => Finset.disjoint_left.mp (bc76_yBuf_box_disjoint L) h hx
  rw [if_neg hx0, if_pos hx]


theorem bc76_collapse_id {L : ℕ} {x : Site 2} (hx0 : x ∉ bc61_boxAround 2 L (0 : Site 2))
    (hxb : x ∉ bc61_boxAround 2 L (bc76_yBuf L)) : bc76_twoBoxCollapse L x = x := by
  unfold bc76_twoBoxCollapse; rw [if_neg hx0, if_neg hxb]


theorem bc76_pt_notMem_box0_of_col {L : ℕ} {k h : ℤ} (hk : (L : ℤ) < k) :
    bc57_pt k h ∉ bc61_boxAround 2 L (0 : Site 2) := by
  rw [bc61_mem_boxAround_zero, mem_box]
  simp only [not_forall, not_le]
  refine ⟨0, ?_⟩
  rw [bc57_pt_fst]; omega


theorem bc76_pt_notMem_boxBuf_of_col {L : ℕ} {k h : ℤ} (hk : k < 3 * (L : ℤ) + 1) :
    bc57_pt k h ∉ bc61_boxAround 2 L (bc76_yBuf L) := by
  rw [bc61_mem_boxAround, mem_box]
  simp only [not_forall, not_le]
  refine ⟨0, ?_⟩
  simp only [Pi.sub_apply, bc76_yBuf]
  rw [bc57_pt_fst, bc57_pt_fst]
  have : (k - (4 * (L : ℤ) + 1)) = k - 4 * (L : ℤ) - 1 := by ring
  omega


theorem bc76_boxBuf_boundary_mem {L : ℕ} {h : ℤ} (hh : h.natAbs ≤ L) :
    bc57_pt (3 * (L : ℤ) + 1) h ∈ bc61_boxAround 2 L (bc76_yBuf L) := by
  rw [bc61_mem_boxAround, mem_box]
  intro i; fin_cases i
  · simp only [Pi.sub_apply, bc76_yBuf]
    change ((bc57_pt (3 * (L : ℤ) + 1) h) 0 - (bc57_pt (4 * (L : ℤ) + 1) 0) 0).natAbs ≤ L
    rw [bc57_pt_fst, bc57_pt_fst]
    have : (3 * (L : ℤ) + 1 - (4 * (L : ℤ) + 1)) = -(L : ℤ) := by ring
    rw [this, Int.natAbs_neg, Int.natAbs_natCast]
  · simp only [Pi.sub_apply, bc76_yBuf]
    change ((bc57_pt (3 * (L : ℤ) + 1) h) 1 - (bc57_pt (4 * (L : ℤ) + 1) 0) 1).natAbs ≤ L
    rw [bc57_pt_snd, bc57_pt_snd]; simpa using hh


theorem bc76_pt_ne_zero_of_height {k h : ℤ} (hh : 1 ≤ h) : bc57_pt k h ≠ (0 : Site 2) := by
  intro heq; rw [bc60_pt_eq_origin_iff] at heq; omega


theorem bc76_line_adj_gn {L : ℕ} {h k : ℤ} (hh : 1 ≤ h)
    (hlo : (L : ℤ) < k) (hhi : k + 1 < 3 * (L : ℤ) + 1) :
    (bc76_twoBoxGn L).Adj (bc57_pt k h) (bc57_pt (k + 1) h) := by
  have hkid : bc76_twoBoxCollapse L (bc57_pt k h) = bc57_pt k h :=
    bc76_collapse_id (bc76_pt_notMem_box0_of_col hlo) (bc76_pt_notMem_boxBuf_of_col (by omega))
  have hk1id : bc76_twoBoxCollapse L (bc57_pt (k + 1) h) = bc57_pt (k + 1) h :=
    bc76_collapse_id (bc76_pt_notMem_box0_of_col (by omega)) (bc76_pt_notMem_boxBuf_of_col hhi)
  have hne : bc57_pt k h ≠ bc57_pt (k + 1) h := by
    intro heq; have := congrArg (fun f => f 0) heq; simp only [bc57_pt_fst] at this; omega
  exact ⟨hne, bc57_pt k h, bc57_pt (k + 1) h, hkid, hk1id, ⟨bc57_pt_adj k h, bc60_open k hh⟩⟩


theorem bc76_line_reach_right {L : ℕ} {h : ℤ} (hh : 1 ≤ h) (j : ℕ)
    (hj : (L : ℤ) + 1 + (j : ℤ) < 3 * (L : ℤ) + 1) :
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) h, by simpa using bc76_pt_ne_zero_of_height hh⟩
      ⟨bc57_pt ((L : ℤ) + 1 + (j : ℤ)) h, by simpa using bc76_pt_ne_zero_of_height hh⟩ := by
  induction j with
  | zero =>
    have : (⟨bc57_pt ((L : ℤ) + 1 + ((0 : ℕ) : ℤ)) h, by simpa using bc76_pt_ne_zero_of_height hh⟩
        : ({(0 : Site 2)}ᶜ : Set (Site 2)))
        = ⟨bc57_pt ((L : ℤ) + 1) h, by simpa using bc76_pt_ne_zero_of_height hh⟩ := by
      apply Subtype.ext; simp
    rw [this]
  | succ i ih =>
    have hjcast : ((L : ℤ) + 1 + ((i + 1 : ℕ) : ℤ)) = (L : ℤ) + 1 + (i : ℤ) + 1 := by push_cast; ring
    have hilt : (L : ℤ) + 1 + (i : ℤ) < 3 * (L : ℤ) + 1 := by push_cast at hj; omega
    have hstep : (bc76_twoBoxGn L).Adj (bc57_pt ((L : ℤ) + 1 + (i : ℤ)) h)
        (bc57_pt ((L : ℤ) + 1 + (i : ℤ) + 1) h) :=
      bc76_line_adj_gn hh (by omega) (by push_cast at hj ⊢; omega)
    have hstep' : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Adj
        ⟨bc57_pt ((L : ℤ) + 1 + (i : ℤ)) h, by simpa using bc76_pt_ne_zero_of_height hh⟩
        ⟨bc57_pt ((L : ℤ) + 1 + (i : ℤ) + 1) h, by
          simpa using bc76_pt_ne_zero_of_height (k := (L : ℤ) + 1 + (i : ℤ) + 1) hh⟩ := hstep
    have hres := (ih hilt).trans hstep'.reachable
    
    have hcongr : (⟨bc57_pt ((L : ℤ) + 1 + (i : ℤ) + 1) h, by
          simpa using bc76_pt_ne_zero_of_height (k := (L : ℤ) + 1 + (i : ℤ) + 1) hh⟩
          : ({(0 : Site 2)}ᶜ : Set (Site 2)))
        = ⟨bc57_pt ((L : ℤ) + 1 + ((i + 1 : ℕ) : ℤ)) h, by
            simpa using bc76_pt_ne_zero_of_height hh⟩ := by
      apply Subtype.ext; simp only; rw [hjcast]
    rw [hcongr] at hres
    exact hres


theorem bc76_glue_adj {L : ℕ} {h : ℤ} (hh : 1 ≤ h) (hhL : h.natAbs ≤ L) :
    (bc76_twoBoxGn L).Adj (bc57_pt (3 * (L : ℤ)) h) (bc76_yBuf L) := by
  have h1id : bc76_twoBoxCollapse L (bc57_pt (3 * (L : ℤ)) h) = bc57_pt (3 * (L : ℤ)) h :=
    bc76_collapse_id (bc76_pt_notMem_box0_of_col (by omega)) (bc76_pt_notMem_boxBuf_of_col (by omega))
  have h2buf : bc76_twoBoxCollapse L (bc57_pt (3 * (L : ℤ) + 1) h) = bc76_yBuf L :=
    bc76_collapse_buf (bc76_boxBuf_boundary_mem hhL)
  have hadj : (openSubgraph 2 bc60_upperLines).Adj (bc57_pt (3 * (L : ℤ)) h)
      (bc57_pt (3 * (L : ℤ) + 1) h) := ⟨bc57_pt_adj (3 * (L : ℤ)) h, bc60_open (3 * (L : ℤ)) hh⟩
  have hne : bc57_pt (3 * (L : ℤ)) h ≠ bc76_yBuf L := by
    intro heq
    have := congrArg (fun f => f 1) heq
    simp only [bc57_pt_snd, bc76_yBuf, bc57_pt_snd] at this
    omega
  exact ⟨hne, bc57_pt (3 * (L : ℤ)) h, bc57_pt (3 * (L : ℤ) + 1) h, h1id, h2buf, hadj⟩


theorem bc76_yBuf_ne_zero (L : ℕ) : bc76_yBuf L ≠ (0 : Site 2) := by
  intro heq; rw [bc76_yBuf, bc60_pt_eq_origin_iff] at heq; omega


theorem bc76_gnCut_reconnect_upperLines {L : ℕ} (hL : 3 ≤ L) :
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
  
  set jn : ℕ := 2 * L - 1 with hjn
  have hjnval : (jn : ℤ) = 2 * (L : ℤ) - 1 := by
    rw [hjn]; have : 1 ≤ 2 * L := by omega
    push_cast [Nat.cast_sub this]; ring
  have hjcol : (L : ℤ) + 1 + (jn : ℤ) = 3 * (L : ℤ) := by rw [hjnval]; ring
  have hjlt : (L : ℤ) + 1 + (jn : ℤ) < 3 * (L : ℤ) + 1 := by rw [hjcol]; omega
  
  have hreach1 : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt (3 * (L : ℤ)) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
    have := bc76_line_reach_right (h := 1) (by norm_num) jn hjlt
    rw [hjcol] at this; exact this
  
  have hreach3 : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt (3 * (L : ℤ)) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
    have := bc76_line_reach_right (h := 3) (by norm_num) jn hjlt
    rw [hjcol] at this; exact this
  
  have hL1 : (1 : ℤ).natAbs ≤ L := by simp only [Int.natAbs_one]; omega
  have hL3 : (3 : ℤ).natAbs ≤ L := by rw [show (3 : ℤ).natAbs = 3 from rfl]; omega
  have hglue1 : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Adj
      ⟨bc57_pt (3 * (L : ℤ)) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc76_yBuf L, by simpa using bc76_yBuf_ne_zero L⟩ :=
    bc76_glue_adj (by norm_num) hL1
  have hglue3 : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Adj
      ⟨bc76_yBuf L, by simpa using bc76_yBuf_ne_zero L⟩
      ⟨bc57_pt (3 * (L : ℤ)) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
    (bc76_glue_adj (by norm_num) hL3).symm
  
  exact ((hreach1.trans hglue1.reachable).trans hglue3.reachable).trans hreach3.symm


theorem bc76_buffer_insufficient {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
  ⟨bc67_upperLines_is_G_n_trifurcation hL, bc76_yBuf_box_disjoint L,
   bc76_gnCut_reconnect_upperLines hL⟩


theorem bc76_status :
    
    (∀ {L : ℕ} {y y' : Site d}, bc76_bufferResVec L y = bc76_bufferResVec L y' → y ≠ y' →
      (∃ i, 4 * L < ((y - y') i).natAbs) ∧
      (∃ i, ∀ x : Site d, ((x - y) i).natAbs ≤ L → 2 * L < ((x - y') i).natAbs)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)) (y s t : Site d),
      y ∈ bc73_fiber ω L R c → s ≠ y → t ≠ y → (bc75_fiberQuot ω L R c).Adj s t →
      ∃ p q, p ∉ bc61_boxAround d L y ∧ q ∉ bc61_boxAround d L y ∧
        bc75_collapseFiber ω L R c p = s ∧ bc75_collapseFiber ω L R c q = t ∧
        (openSubgraph d ω).Adj p q) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
      Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
      ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
        ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
        ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L y y' hres hne
    exact ⟨bc76_far_of_sameBufferResidue hres hne, bc76_bufferGap hres hne⟩
  · intro ω L R c y s t hy hs ht hadj; exact bc76_fiberQuotEdge_lifts hy hs ht hadj
  · intro L hL; exact bc76_buffer_insufficient hL

end StatMech.Walls
