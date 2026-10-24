import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundary
open Finset Set SimpleGraph StatMech StatMech.FrontierA


/--
[bgf2_deleted_reachable_of_cut_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma bgf2_deleted_reachable_of_cut_connected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {a b : Site 2}
-- given
  (h0 : bgf2_IndexAllOpen omega L 0)
  (h : Connected 2 (removeSites (bc61_boxAround 2 L 0) omega) a b) :
-- imply
  (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable (bgf2_q omega L a) (bgf2_q omega L b) := by
-- proof
  apply StatMech.FrontierA.bgf2_deleted_reachable_of_cut_connected h0 h

/--
[bgf2_q_eq_centre_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma bgf2_q_eq_centre_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j x : Site 2}
-- given
  (hj : bgf2_IndexAllOpen omega L j) :
-- imply
  bgf2_q omega L x = bgf2_centre L j ↔ bgn_idx L x = j := by
-- proof
  apply StatMech.FrontierA.bgf2_q_eq_centre_iff hj

/--
[bgf2_mem_box_centre_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma bgf2_mem_box_centre_iff_eq
  {L : ℕ}
  {j x : Site 2} :
-- imply
  x ∈ bc61_boxAround 2 L (bgf2_centre L j) ↔ bgn_idx L x = j := by
-- proof
  apply StatMech.FrontierA.bgf2_mem_box_centre_iff

/--
[bgf2_indexAllOpen_cut_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma bgf2_indexAllOpen_cut_at_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j k : Site 2}
-- given
  (hk : bgf2_IndexAllOpen omega L k)
  (hkj : k ≠ j) :
-- imply
  bgf2_IndexAllOpen (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) L k := by
-- proof
  apply StatMech.FrontierA.bgf2_indexAllOpen_cut_at hk hkj

/--
[bgf2_cut_q_eq_connected_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma bgf2_cut_q_eq_connected_at_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j a b : Site 2}
-- given
  (hj : bgf2_IndexAllOpen omega L j)
  (h : bgf2_q omega L a = bgf2_q omega L b)
  (hne : bgf2_q omega L a ≠ bgf2_centre L j) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a b := by
-- proof
  apply StatMech.FrontierA.bgf2_cut_q_eq_connected_at hj h hne

/--
[bgf2_cut_connected_of_reach_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma bgf2_cut_connected_of_reach_at_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j : Site 2}
-- given
  (hj : bgf2_IndexAllOpen omega L j) :
-- imply
  ∀ {u v : Site 2}, (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable u v → ∀ a b, bgf2_q omega L a = u → bgf2_q omega L b = v → u ≠ bgf2_centre L j → v ≠ bgf2_centre L j → Connected 2 (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a b := by
-- proof
  apply StatMech.FrontierA.bgf2_cut_connected_of_reach_at hj

/--
[faithfulAllOpenTrifAt_boundary_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma faithfulAllOpenTrifAt_boundary_witnesses_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
  {j : Site 2}
-- given
  (hR : 1 ≤ R)
  (h : FaithfulAllOpenTrifAt omega L j)
  (harms : ∀ a : Site 2, bc67_GnIncident omega L (bgf2_centre L j) a → (cluster 2 (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a).Infinite → a ∈ box 2 R) :
-- imply
  ∃ z1 z2 z3 : Site 2, z1 ∈ vertexBoundary 2 R ∧ z2 ∈ vertexBoundary 2 R ∧ z3 ∈ vertexBoundary 2 R ∧ bgf2_q omega L z1 ≠ bgf2_centre L j ∧ bgf2_q omega L z2 ≠ bgf2_centre L j ∧ bgf2_q omega L z3 ≠ bgf2_centre L j ∧ (bgf2_Gf omega L).Reachable (bgf2_centre L j) (bgf2_q omega L z1) ∧ (bgf2_Gf omega L).Reachable (bgf2_centre L j) (bgf2_q omega L z2) ∧ (bgf2_Gf omega L).Reachable (bgf2_centre L j) (bgf2_q omega L z3) ∧ ¬ (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable (bgf2_q omega L z1) (bgf2_q omega L z2) ∧ ¬ (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable (bgf2_q omega L z1) (bgf2_q omega L z3) ∧ ¬ (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable (bgf2_q omega L z2) (bgf2_q omega L z3) := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpenTrifAt_boundary_witnesses hR h harms

/--
[faithfulAllOpenTrifAt_count_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma faithfulAllOpenTrifAt_count_le_boundary_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
  {J : Finset (Site 2)}
-- given
  (hR : 1 ≤ R)
  (htrif : ∀ j ∈ J, FaithfulAllOpenTrifAt omega L j)
  (harms : ∀ j ∈ J, ∀ a : Site 2, bc67_GnIncident omega L (bgf2_centre L j) a → (cluster 2 (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a).Infinite → a ∈ box 2 R) :
-- imply
  J.card ≤ (vertexBoundary_finite 2 R).toFinset.card := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpenTrifAt_count_le_boundary omega L R hR J htrif harms

/--
[gnIncident_arm_mem_outer_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma gnIncident_arm_mem_outer_box_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L N : ℕ}
  {j a : Site 2}
-- given
  (hc : bgf2_centre L j ∈ box 2 N)
  (hi : bc67_GnIncident omega L (bgf2_centre L j) a) :
-- imply
  a ∈ box 2 (N + L + 1) := by
-- proof
  apply StatMech.FrontierA.gnIncident_arm_mem_outer_box hc hi

/--
[faithfulAllOpenTrifAt_count_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma faithfulAllOpenTrifAt_count_inner_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L N : ℕ}
  {J : Finset (Site 2)}
-- given
  (htrif : ∀ j ∈ J, FaithfulAllOpenTrifAt omega L j)
  (hcenter : ∀ j ∈ J, bgf2_centre L j ∈ box 2 N) :
-- imply
  J.card ≤ (vertexBoundary_finite 2 (N + L + 1)).toFinset.card := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpenTrifAt_count_inner omega L N J htrif hcenter

/--
[bgf2_centre_mem_scaled_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma bgf2_centre_mem_scaled_box_eq
  {L N : ℕ}
  {j : Site 2}
-- given
  (hj : j ∈ box 2 N) :
-- imply
  bgf2_centre L j ∈ box 2 ((2 * L + 1) * N) := by
-- proof
  apply StatMech.FrontierA.bgf2_centre_mem_scaled_box hj

/--
[mem_faithfulAllOpenTrifIndicesInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma mem_faithfulAllOpenTrifIndicesInBox_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L N : ℕ}
  {j : Site 2} :
-- imply
  j ∈ faithfulAllOpenTrifIndicesInBox omega L N ↔ j ∈ box 2 N ∧ FaithfulAllOpenTrifAt omega L j := by
-- proof
  apply StatMech.FrontierA.mem_faithfulAllOpenTrifIndicesInBox

/--
[faithfulAllOpenTrifIndicesInBox_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma faithfulAllOpenTrifIndicesInBox_count_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L N : ℕ} :
-- imply
  (faithfulAllOpenTrifIndicesInBox omega L N).card ≤ (vertexBoundary_finite 2 ((2 * L + 1) * N + L + 1)).toFinset.card := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpenTrifIndicesInBox_count omega L N

/--
[allOpenTrif_boundary_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean)
-/
@[path]
private lemma allOpenTrif_boundary_witnesses_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (hR : 1 ≤ R)
  (h : bao_AllOpenTrif omega L)
  (harms : ∀ a : Site 2, bc67_GnIncident omega L 0 a → (cluster 2 (removeSites (bc61_boxAround 2 L 0) omega) a).Infinite → a ∈ box 2 R) :
-- imply
  ∃ z1 z2 z3 : Site 2, z1 ∈ vertexBoundary 2 R ∧ z2 ∈ vertexBoundary 2 R ∧ z3 ∈ vertexBoundary 2 R ∧ bgf2_q omega L z1 ≠ 0 ∧ bgf2_q omega L z2 ≠ 0 ∧ bgf2_q omega L z3 ≠ 0 ∧ (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z1) ∧ (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z2) ∧ (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z3) ∧ ¬ (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable (bgf2_q omega L z1) (bgf2_q omega L z2) ∧ ¬ (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable (bgf2_q omega L z1) (bgf2_q omega L z3) ∧ ¬ (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable (bgf2_q omega L z2) (bgf2_q omega L z3) := by
-- proof
  apply StatMech.FrontierA.allOpenTrif_boundary_witnesses hR h harms


-- created on 2026-10-23
