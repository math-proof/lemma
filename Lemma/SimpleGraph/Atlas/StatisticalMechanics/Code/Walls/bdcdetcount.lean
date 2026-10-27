import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bdcdetcount.Part3
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bdc_allOpen_indexAllOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_allOpen_indexAllOpen_eq
  {L : ℕ}
  {j : Site 2} :
-- imply
  bgf2_IndexAllOpen bdc_allOpenCfg L j := by
-- proof
  apply StatMech.Walls.bdc_allOpen_indexAllOpen L j

/--
[bdc_idx_ptL0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_idx_ptL0_eq
  {L : ℕ} :
-- imply
  bgn_idx L (bc57_pt (L : ℤ) 0) = 0 := by
-- proof
  apply StatMech.Walls.bdc_idx_ptL0 L

/--
[bdc_idx_ptL10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_idx_ptL10_eq
  {L : ℕ} :
-- imply
  bgn_idx L (bc57_pt ((L : ℤ) + 1) 0) = bc57_pt 1 0 := by
-- proof
  apply StatMech.Walls.bdc_idx_ptL10 L

/--
[bdc_q_ptL0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_q_ptL0_eq
  {L : ℕ} :
-- imply
  bgf2_q bdc_allOpenCfg L (bc57_pt (L : ℤ) 0) = 0 := by
-- proof
  apply StatMech.Walls.bdc_q_ptL0 L

/--
[bdc_q_ptL10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_q_ptL10_eq
  {L : ℕ} :
-- imply
  bgf2_q bdc_allOpenCfg L (bc57_pt ((L : ℤ) + 1) 0) = bc57_pt (2 * (L : ℤ) + 1) 0 := by
-- proof
  apply StatMech.Walls.bdc_q_ptL10 L

/--
[bdc_Gf_centre_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_Gf_centre_edge_eq
  {L : ℕ} :
-- imply
  (bgf2_Gf bdc_allOpenCfg L).Adj 0 (bc57_pt (2 * (L : ℤ) + 1) 0) := by
-- proof
  apply StatMech.Walls.bdc_Gf_centre_edge L

/--
[bdc_Gf_not_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_Gf_not_le_lattice_eq
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  ¬ (bgf2_Gf bdc_allOpenCfg L ≤ hypercubicLattice 2) := by
-- proof
  apply StatMech.Walls.bdc_Gf_not_le_lattice hL

/--
[bdc_datum_implies_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_datum_implies_count_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bau_ArmSubforestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bdc_datum_implies_count ω L R h

/--
[bdc_shiftCfg_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_shiftCfg_edge_eq
  {c : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2} :
-- imply
  bdc_shiftCfg c ω s(x, y) = ω s(x + c, y + c) := by
-- proof
  apply StatMech.Walls.bdc_shiftCfg_edge c ω x y

/--
[bdc_lat_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_lat_shift_eq
  {c x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj (x + c) (y + c) ↔ (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.Walls.bdc_lat_shift c x y

/--
[bdc_openSub_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_openSub_shift_eq
  {c : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2} :
-- imply
  (openSubgraph 2 (bdc_shiftCfg c ω)).Adj x y ↔ (openSubgraph 2 ω).Adj (x + c) (y + c) := by
-- proof
  apply StatMech.Walls.bdc_openSub_shift c ω x y

/--
[bdc_bgn_idx_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_bgn_idx_shift_eq
  {L : ℕ}
  {j x : Site 2} :
-- imply
  bgn_idx L (x + bgf2_centre L j) = bgn_idx L x + j := by
-- proof
  apply StatMech.Walls.bdc_bgn_idx_shift L j x

/--
[bdc_centre_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_centre_add_eq
  {L : ℕ}
  {a b : Site 2} :
-- imply
  bgf2_centre L (a + b) = bgf2_centre L a + bgf2_centre L b := by
-- proof
  apply StatMech.Walls.bdc_centre_add L a b

/--
[bdc_indexAllOpen_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_indexAllOpen_shift_eq
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j k : Site 2} :
-- imply
  bgf2_IndexAllOpen (bdc_shiftCfg (bgf2_centre L j) ω) L k ↔ bgf2_IndexAllOpen ω L (k + j) := by
-- proof
  apply StatMech.Walls.bdc_indexAllOpen_shift L ω j k

/--
[bdc_q_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_q_shift_eq
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j x : Site 2} :
-- imply
  bgf2_q (bdc_shiftCfg (bgf2_centre L j) ω) L x = bgf2_q ω L (x + bgf2_centre L j) - bgf2_centre L j := by
-- proof
  apply StatMech.Walls.bdc_q_shift L ω j x

/--
[bdc_Gf_shift_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_Gf_shift_adj_eq
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j u v : Site 2} :
-- imply
  (bgf2_Gf (bdc_shiftCfg (bgf2_centre L j) ω) L).Adj u v ↔ (bgf2_Gf ω L).Adj (u + bgf2_centre L j) (v + bgf2_centre L j) := by
-- proof
  apply StatMech.Walls.bdc_Gf_shift_adj L ω j u v

/--
[bdc_cut_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_cut_transport_eq
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j w₁ w₂ : Site 2}
-- given
  (h : ¬ (bkg_deleteVertex (bgf2_Gf (bdc_shiftCfg (bgf2_centre L j) ω) L) 0).Reachable w₁ w₂) :
-- imply
  ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (w₁ + bgf2_centre L j) (w₂ + bgf2_centre L j) := by
-- proof
  apply StatMech.Walls.bdc_cut_transport L ω j w₁ w₂ h

/--
[bdc_trif_separation_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_trif_separation_at_eq
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j : Site 2}
-- given
  (h : bao_AllOpenTrif (bdc_shiftCfg (bgf2_centre L j) ω) L) :
-- imply
  ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ bgf2_centre L j ∧ w₂ ≠ bgf2_centre L j ∧ w₃ ≠ bgf2_centre L j ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₂ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₃ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₂ w₃ := by
-- proof
  apply StatMech.Walls.bdc_trif_separation_at L ω j h

/--
[bdc_shiftCfg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_shiftCfg_zero_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  bdc_shiftCfg 0 ω = ω := by
-- proof
  apply StatMech.Walls.bdc_shiftCfg_zero ω

/--
[bdc_trif_separation_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_trif_separation_at_zero_eq
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : bao_AllOpenTrif ω L) :
-- imply
  ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0 ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃ := by
-- proof
  apply StatMech.Walls.bdc_trif_separation_at_zero L ω h

/--
[bdc_hub_feed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_hub_feed_eq
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j : Site 2}
  {S : Finset (Site 2)}
-- given
  (h : bao_AllOpenTrif (bdc_shiftCfg (bgf2_centre L j) ω) L)
  (hcS : bgf2_centre L j ∈ S)
  (hmem : ∀ w₁ w₂ w₃ : Site 2, w₁ ≠ bgf2_centre L j → w₂ ≠ bgf2_centre L j → w₃ ≠ bgf2_centre L j → w₁ ∈ S ∧ w₂ ∈ S ∧ w₃ ∈ S) :
-- imply
  ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ (⟨bgf2_centre L j, hcS⟩ : {v // v ∈ S}) ∧ a₂ ≠ ⟨bgf2_centre L j, hcS⟩ ∧ a₃ ≠ ⟨bgf2_centre L j, hcS⟩ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (a₁ : Site 2) (a₂ : Site 2) ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (a₁ : Site 2) (a₃ : Site 2) ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (a₂ : Site 2) (a₃ : Site 2) := by
-- proof
  apply StatMech.Walls.bdc_hub_feed L ω j h hcS hmem

/--
[bdc_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean)
-/
@[path]
private lemma bdc_status_eq :
-- imply
  (∀ L : ℕ, 1 ≤ L → ¬ (bgf2_Gf bdc_allOpenCfg L ≤ hypercubicLattice 2)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧ (∀ (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j : Site 2), bao_AllOpenTrif (bdc_shiftCfg (bgf2_centre L j) ω) L → ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ bgf2_centre L j ∧ w₂ ≠ bgf2_centre L j ∧ w₃ ≠ bgf2_centre L j ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₂ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₃ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₂ w₃) := by
-- proof
  apply StatMech.Walls.bdc_status


-- created on 2026-10-23
