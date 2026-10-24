import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.AllOpenContractionGeneral
open Set SimpleGraph Finset StatMech StatMech.FrontierA


/--
[bgfdGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfdGraph_adj_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {u v : Site d} :
-- imply
  (bgfdGraph omega L).Adj u v ↔ u ≠ v ∧ ∃ a b : Site d, bgfdQ omega L a = u ∧ bgfdQ omega L b = v ∧ (openSubgraph d omega).Adj a b := by
-- proof
  apply StatMech.FrontierA.bgfdGraph_adj omega L u v

/--
[bgfd_q_eq_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_q_eq_connected_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {a b : Site d}
-- given
  (h : bgfdQ omega L a = bgfdQ omega L b) :
-- imply
  Connected d omega a b := by
-- proof
  apply StatMech.FrontierA.bgfd_q_eq_connected h

/--
[bgfd_reach_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_reach_of_connected_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {a b : Site d}
-- given
  (h : Connected d omega a b) :
-- imply
  (bgfdGraph omega L).Reachable (bgfdQ omega L a) (bgfdQ omega L b) := by
-- proof
  apply StatMech.FrontierA.bgfd_reach_of_connected h

/--
[bgfd_connected_of_reach_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_connected_of_reach_aux_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ} :
-- imply
  ∀ {u v : Site d}, (bgfdGraph omega L).Reachable u v → ∀ a b, bgfdQ omega L a = u → bgfdQ omega L b = v → Connected d omega a b := by
-- proof
  apply StatMech.FrontierA.bgfd_connected_of_reach_aux

/--
[bgfd_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_faithful_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {a b : Site d} :
-- imply
  (bgfdGraph omega L).Reachable (bgfdQ omega L a) (bgfdQ omega L b) ↔ Connected d omega a b := by
-- proof
  apply StatMech.FrontierA.bgfd_faithful omega L a b

/--
[bgfd_mem_box0_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_mem_box0_iff_eq
  {d : ℕ}
  {L : ℕ}
  {x : Site d} :
-- imply
  x ∈ bc61_boxAround d L 0 ↔ bgn_idx L x = 0 := by
-- proof
  apply StatMech.FrontierA.bgfd_mem_box0_iff

/--
[bgfd_q_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_q_eq_zero_iff_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x : Site d}
-- given
  (h0 : BgfdIndexAllOpen omega L 0) :
-- imply
  bgfdQ omega L x = 0 ↔ bgn_idx L x = 0 := by
-- proof
  apply StatMech.FrontierA.bgfd_q_eq_zero_iff h0

/--
[bgfd_q_eq_zero_iff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_q_eq_zero_iff_mem_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x : Site d}
-- given
  (h0 : BgfdIndexAllOpen omega L 0) :
-- imply
  bgfdQ omega L x = 0 ↔ x ∈ bc61_boxAround d L 0 := by
-- proof
  apply StatMech.FrontierA.bgfd_q_eq_zero_iff_mem h0

/--
[bgfd_indexAllOpen_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_indexAllOpen_cut_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j : Site d}
-- given
  (h : BgfdIndexAllOpen omega L j)
  (hj : j ≠ 0) :
-- imply
  BgfdIndexAllOpen (removeSites (bc61_boxAround d L 0) omega) L j := by
-- proof
  apply StatMech.FrontierA.bgfd_indexAllOpen_cut h hj

/--
[bgfd_cut_q_eq_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_cut_q_eq_connected_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {a b : Site d}
-- given
  (h0 : BgfdIndexAllOpen omega L 0)
  (h : bgfdQ omega L a = bgfdQ omega L b)
  (hne : bgfdQ omega L a ≠ 0) :
-- imply
  Connected d (removeSites (bc61_boxAround d L 0) omega) a b := by
-- proof
  apply StatMech.FrontierA.bgfd_cut_q_eq_connected h0 h hne

/--
[bgfd_cut_connected_of_reach_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_cut_connected_of_reach_aux_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
-- given
  (h0 : BgfdIndexAllOpen omega L 0) :
-- imply
  ∀ {u v : Site d}, (bkg_deleteVertex (bgfdGraph omega L) 0).Reachable u v → ∀ a b, bgfdQ omega L a = u → bgfdQ omega L b = v → u ≠ 0 → v ≠ 0 → Connected d (removeSites (bc61_boxAround d L 0) omega) a b := by
-- proof
  apply StatMech.FrontierA.bgfd_cut_connected_of_reach_aux h0

/--
[bgfd_mem_box_centre_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_mem_box_centre_iff_eq
  {d : ℕ}
  {L : ℕ}
  {j x : Site d} :
-- imply
  x ∈ bc61_boxAround d L (bgfdCentre L j) ↔ bgn_idx L x = j := by
-- proof
  apply StatMech.FrontierA.bgfd_mem_box_centre_iff

/--
[bgfd_q_eq_centre_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_q_eq_centre_iff_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j x : Site d}
-- given
  (hj : BgfdIndexAllOpen omega L j) :
-- imply
  bgfdQ omega L x = bgfdCentre L j ↔ bgn_idx L x = j := by
-- proof
  apply StatMech.FrontierA.bgfd_q_eq_centre_iff hj

/--
[bgfd_indexAllOpen_cut_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_indexAllOpen_cut_at_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j k : Site d}
-- given
  (hk : BgfdIndexAllOpen omega L k)
  (hkj : k ≠ j) :
-- imply
  BgfdIndexAllOpen (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) L k := by
-- proof
  apply StatMech.FrontierA.bgfd_indexAllOpen_cut_at hk hkj

/--
[bgfd_cut_q_eq_connected_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_cut_q_eq_connected_at_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j a b : Site d}
-- given
  (hj : BgfdIndexAllOpen omega L j)
  (h : bgfdQ omega L a = bgfdQ omega L b)
  (hne : bgfdQ omega L a ≠ bgfdCentre L j) :
-- imply
  Connected d (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a b := by
-- proof
  apply StatMech.FrontierA.bgfd_cut_q_eq_connected_at hj h hne

/--
[bgfd_cut_connected_of_reach_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_cut_connected_of_reach_at_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j : Site d}
-- given
  (hj : BgfdIndexAllOpen omega L j) :
-- imply
  ∀ {u v : Site d}, (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable u v → ∀ a b, bgfdQ omega L a = u → bgfdQ omega L b = v → u ≠ bgfdCentre L j → v ≠ bgfdCentre L j → Connected d (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a b := by
-- proof
  apply StatMech.FrontierA.bgfd_cut_connected_of_reach_at hj

/--
[bgfd_deleted_reachable_of_cut_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean)
-/
@[path]
private lemma bgfd_deleted_reachable_of_cut_connected_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j : Site d}
  {a b : Site d}
-- given
  (hj : BgfdIndexAllOpen omega L j)
  (h : Connected d (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a b) :
-- imply
  (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable (bgfdQ omega L a) (bgfdQ omega L b) := by
-- proof
  apply StatMech.FrontierA.bgfd_deleted_reachable_of_cut_connected hj h


-- created on 2026-10-23
