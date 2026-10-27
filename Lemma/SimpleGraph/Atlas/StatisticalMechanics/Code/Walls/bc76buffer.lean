import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc76buffer.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc76_far_of_sameBufferResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_far_of_sameBufferResidue_eq
  {d : ℕ}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hres : bc76_bufferResVec L y = bc76_bufferResVec L y')
  (hne : y ≠ y') :
-- imply
  ∃ i, 4 * L < ((y - y') i).natAbs := by
-- proof
  apply StatMech.Walls.bc76_far_of_sameBufferResidue hres hne

/--
[bc76_bufferFiber_boxes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_bufferFiber_boxes_disjoint_eq
  {d : ℕ}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hres : bc76_bufferResVec L y = bc76_bufferResVec L y')
  (hne : y ≠ y') :
-- imply
  Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
-- proof
  apply StatMech.Walls.bc76_bufferFiber_boxes_disjoint hres hne

/--
[bc76_bufferGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_bufferGap_eq
  {d : ℕ}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hres : bc76_bufferResVec L y = bc76_bufferResVec L y')
  (hne : y ≠ y') :
-- imply
  ∃ i, ∀ x : Site d, ((x - y) i).natAbs ≤ L → 2 * L < ((x - y') i).natAbs := by
-- proof
  apply StatMech.Walls.bc76_bufferGap hres hne

/--
[bc76_fiberQuotEdge_lifts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_fiberQuotEdge_lifts_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {y s t : Site d}
-- given
  (hy : y ∈ bc73_fiber ω L R c)
  (hs : s ≠ y)
  (ht : t ≠ y)
  (hadj : (bc75_fiberQuot ω L R c).Adj s t) :
-- imply
  ∃ p q, p ∉ bc61_boxAround d L y ∧ q ∉ bc61_boxAround d L y ∧ bc75_collapseFiber ω L R c p = s ∧ bc75_collapseFiber ω L R c q = t ∧ (openSubgraph d ω).Adj p q := by
-- proof
  apply StatMech.Walls.bc76_fiberQuotEdge_lifts hy hs ht hadj

/--
[bc76_yBuf_box_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_yBuf_box_disjoint_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) := by
-- proof
  apply StatMech.Walls.bc76_yBuf_box_disjoint L

/--
[bc76_collapse_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_collapse_zero_eq
  {d : ℕ}
  {L : ℕ}
  {x : Site 2}
-- given
  (hx : x ∈ bc61_boxAround 2 L (0 : Site 2)) :
-- imply
  bc76_twoBoxCollapse L x = 0 := by
-- proof
  apply StatMech.Walls.bc76_collapse_zero hx

/--
[bc76_collapse_buf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_collapse_buf_eq
  {d : ℕ}
  {L : ℕ}
  {x : Site 2}
-- given
  (hx : x ∈ bc61_boxAround 2 L (bc76_yBuf L)) :
-- imply
  bc76_twoBoxCollapse L x = bc76_yBuf L := by
-- proof
  apply StatMech.Walls.bc76_collapse_buf hx

/--
[bc76_collapse_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_collapse_id_eq
  {d : ℕ}
  {L : ℕ}
  {x : Site 2}
-- given
  (hx0 : x ∉ bc61_boxAround 2 L (0 : Site 2))
  (hxb : x ∉ bc61_boxAround 2 L (bc76_yBuf L)) :
-- imply
  bc76_twoBoxCollapse L x = x := by
-- proof
  apply StatMech.Walls.bc76_collapse_id hx0 hxb

/--
[bc76_pt_notMem_box0_of_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_pt_notMem_box0_of_col_eq
  {d : ℕ}
  {L : ℕ}
  {k h : ℤ}
-- given
  (hk : (L : ℤ) < k) :
-- imply
  bc57_pt k h ∉ bc61_boxAround 2 L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc76_pt_notMem_box0_of_col hk

/--
[bc76_pt_notMem_boxBuf_of_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_pt_notMem_boxBuf_of_col_eq
  {d : ℕ}
  {L : ℕ}
  {k h : ℤ}
-- given
  (hk : k < 3 * (L : ℤ) + 1) :
-- imply
  bc57_pt k h ∉ bc61_boxAround 2 L (bc76_yBuf L) := by
-- proof
  apply StatMech.Walls.bc76_pt_notMem_boxBuf_of_col hk

/--
[bc76_boxBuf_boundary_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_boxBuf_boundary_mem_eq
  {d : ℕ}
  {L : ℕ}
  {h : ℤ}
-- given
  (hh : h.natAbs ≤ L) :
-- imply
  bc57_pt (3 * (L : ℤ) + 1) h ∈ bc61_boxAround 2 L (bc76_yBuf L) := by
-- proof
  apply StatMech.Walls.bc76_boxBuf_boundary_mem hh

/--
[bc76_pt_ne_zero_of_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_pt_ne_zero_of_height_eq
  {d : ℕ}
  {k h : ℤ}
-- given
  (hh : 1 ≤ h) :
-- imply
  bc57_pt k h ≠ (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc76_pt_ne_zero_of_height hh

/--
[bc76_line_adj_gn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_line_adj_gn_eq
  {d : ℕ}
  {L : ℕ}
  {h k : ℤ}
-- given
  (hh : 1 ≤ h)
  (hlo : (L : ℤ) < k)
  (hhi : k + 1 < 3 * (L : ℤ) + 1) :
-- imply
  (bc76_twoBoxGn L).Adj (bc57_pt k h) (bc57_pt (k + 1) h) := by
-- proof
  apply StatMech.Walls.bc76_line_adj_gn hh hlo hhi

/--
[bc76_line_reach_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_line_reach_right_eq
  {d : ℕ}
  {L : ℕ}
  {h : ℤ}
  {j : ℕ}
-- given
  (hh : 1 ≤ h)
  (hj : (L : ℤ) + 1 + (j : ℤ) < 3 * (L : ℤ) + 1) :
-- imply
  ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) h, by simpa using bc76_pt_ne_zero_of_height hh⟩ ⟨bc57_pt ((L : ℤ) + 1 + (j : ℤ)) h, by simpa using bc76_pt_ne_zero_of_height hh⟩ := by
-- proof
  apply StatMech.Walls.bc76_line_reach_right hh j hj

/--
[bc76_glue_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_glue_adj_eq
  {d : ℕ}
  {L : ℕ}
  {h : ℤ}
-- given
  (hh : 1 ≤ h)
  (hhL : h.natAbs ≤ L) :
-- imply
  (bc76_twoBoxGn L).Adj (bc57_pt (3 * (L : ℤ)) h) (bc76_yBuf L) := by
-- proof
  apply StatMech.Walls.bc76_glue_adj hh hhL

/--
[bc76_yBuf_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_yBuf_ne_zero_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  bc76_yBuf L ≠ (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc76_yBuf_ne_zero L

/--
[bc76_gnCut_reconnect_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_gnCut_reconnect_upperLines_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
-- proof
  apply StatMech.Walls.bc76_gnCut_reconnect_upperLines hL

/--
[bc76_buffer_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_buffer_insufficient_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧ ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
-- proof
  apply StatMech.Walls.bc76_buffer_insufficient hL

/--
[bc76_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean)
-/
@[path]
private lemma bc76_status_eq
  {d : ℕ} :
-- imply
  (∀ {L : ℕ} {y y' : Site d}, bc76_bufferResVec L y = bc76_bufferResVec L y' → y ≠ y' → (∃ i, 4 * L < ((y - y') i).natAbs) ∧ (∃ i, ∀ x : Site d, ((x - y) i).natAbs ≤ L → 2 * L < ((x - y') i).natAbs)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)) (y s t : Site d), y ∈ bc73_fiber ω L R c → s ≠ y → t ≠ y → (bc75_fiberQuot ω L R c).Adj s t → ∃ p q, p ∉ bc61_boxAround d L y ∧ q ∉ bc61_boxAround d L y ∧ bc75_collapseFiber ω L R c p = s ∧ bc75_collapseFiber ω L R c q = t ∧ (openSubgraph d ω).Adj p q) ∧ (∀ {L : ℕ}, 3 ≤ L → bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧ ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) := by
-- proof
  apply StatMech.Walls.bc76_status


-- created on 2026-10-23
