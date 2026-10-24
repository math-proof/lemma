import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bgf2faithcontract
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bgf2_update_inBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_update_inBox_eq
  {L : ℕ}
  {c x : Site 2}
  {j : Fin 2}
  {v : ℤ}
-- given
  (hx : bgf2_inBox L c x)
  (hv : (v - c j).natAbs ≤ L) :
-- imply
  bgf2_inBox L c (Function.update x j v) := by
-- proof
  apply StatMech.Walls.bgf2_update_inBox hx j hv

/--
[bgf2_mix_inBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_mix_inBox_eq
  {L : ℕ}
  {c x y : Site 2}
  {k : ℕ}
-- given
  (hx : bgf2_inBox L c x)
  (hy : bgf2_inBox L c y) :
-- imply
  bgf2_inBox L c (mixSite x y k) := by
-- proof
  apply StatMech.Walls.bgf2_mix_inBox hx hy k

/--
[bgf2_ascend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_ascend_eq
  {L : ℕ}
  {c : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2}
  {j : Fin 2}
-- given
  (hopen : bgf2_AllOpenAt ω L c)
  (hx : bgf2_inBox L c x) :
-- imply
  ∀ (k : ℕ) (a : ℤ), (a - c j).natAbs ≤ L → (a + (k : ℤ) - c j).natAbs ≤ L → Connected 2 ω (Function.update x j a) (Function.update x j (a + (k : ℤ))) := by
-- proof
  apply StatMech.Walls.bgf2_ascend hopen hx j

/--
[bgf2_update_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_update_conn_eq
  {L : ℕ}
  {c : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2}
  {j : Fin 2}
  {a : ℤ}
-- given
  (hopen : bgf2_AllOpenAt ω L c)
  (hx : bgf2_inBox L c x)
  (ha : (a - c j).natAbs ≤ L) :
-- imply
  Connected 2 ω x (Function.update x j a) := by
-- proof
  apply StatMech.Walls.bgf2_update_conn hopen hx j ha

/--
[bgf2_mix_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_mix_conn_eq
  {L : ℕ}
  {c : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
-- given
  (hopen : bgf2_AllOpenAt ω L c)
  (hx : bgf2_inBox L c x)
  (hy : bgf2_inBox L c y) :
-- imply
  ∀ k, k ≤ 2 → Connected 2 ω x (mixSite x y k) := by
-- proof
  apply StatMech.Walls.bgf2_mix_conn hopen hx hy

/--
[bgf2_boxCentre_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_boxCentre_connected_eq
  {L : ℕ}
  {c : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b : Site 2}
-- given
  (hopen : bgf2_AllOpenAt ω L c)
  (ha : bgf2_inBox L c a)
  (hb : bgf2_inBox L c b) :
-- imply
  Connected 2 ω a b := by
-- proof
  apply StatMech.Walls.bgf2_boxCentre_connected hopen ha hb

/--
[bgf2_idx_iff_inBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_idx_iff_inBox_eq
  {L : ℕ}
  {j x : Site 2} :
-- imply
  bgn_idx L x = j ↔ bgf2_inBox L (bgf2_centre L j) x := by
-- proof
  apply StatMech.Walls.bgf2_idx_iff_inBox

/--
[bgf2_idx_centre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_idx_centre_eq
  {L : ℕ}
  {j : Site 2} :
-- imply
  bgn_idx L (bgf2_centre L j) = j := by
-- proof
  apply StatMech.Walls.bgf2_idx_centre L j

/--
[bgf2_centre_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_centre_inj_eq
  {L : ℕ}
  {j k : Site 2}
-- given
  (h : bgf2_centre L j = bgf2_centre L k) :
-- imply
  j = k := by
-- proof
  apply StatMech.Walls.bgf2_centre_inj h

/--
[bgf2_indexAllOpen_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_indexAllOpen_connected_eq
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j : Site 2}
  {a b : Site 2}
-- given
  (h : bgf2_IndexAllOpen ω L j)
  (ha : bgn_idx L a = j)
  (hb : bgn_idx L b = j) :
-- imply
  Connected 2 ω a b := by
-- proof
  apply StatMech.Walls.bgf2_indexAllOpen_connected h ha hb

/--
[bgf2_Gf_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_Gf_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {u v : Site 2} :
-- imply
  (bgf2_Gf ω L).Adj u v ↔ u ≠ v ∧ ∃ a b : Site 2, bgf2_q ω L a = u ∧ bgf2_q ω L b = v ∧ (openSubgraph 2 ω).Adj a b := by
-- proof
  apply StatMech.Walls.bgf2_Gf_adj ω L u v

/--
[bgf2_q_eq_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_q_eq_connected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {a b : Site 2}
-- given
  (h : bgf2_q ω L a = bgf2_q ω L b) :
-- imply
  Connected 2 ω a b := by
-- proof
  apply StatMech.Walls.bgf2_q_eq_connected h

/--
[bgf2_reach_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_reach_of_connected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {a b : Site 2}
-- given
  (h : Connected 2 ω a b) :
-- imply
  (bgf2_Gf ω L).Reachable (bgf2_q ω L a) (bgf2_q ω L b) := by
-- proof
  apply StatMech.Walls.bgf2_reach_of_connected h

/--
[bgf2_connected_of_reach_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_connected_of_reach_aux_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ} :
-- imply
  ∀ {u v : Site 2}, (bgf2_Gf ω L).Reachable u v → ∀ a b, bgf2_q ω L a = u → bgf2_q ω L b = v → Connected 2 ω a b := by
-- proof
  apply StatMech.Walls.bgf2_connected_of_reach_aux

/--
[bgf2_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_faithful_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {a b : Site 2} :
-- imply
  (bgf2_Gf ω L).Reachable (bgf2_q ω L a) (bgf2_q ω L b) ↔ Connected 2 ω a b := by
-- proof
  apply StatMech.Walls.bgf2_faithful ω L a b

/--
[bgf2_centre_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_centre_zero_eq
  {L : ℕ} :
-- imply
  bgf2_centre L 0 = 0 := by
-- proof
  apply StatMech.Walls.bgf2_centre_zero L

/--
[bgf2_mem_box0_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_mem_box0_iff_eq
  {L : ℕ}
  {x : Site 2} :
-- imply
  x ∈ bc61_boxAround 2 L 0 ↔ bgn_idx L x = 0 := by
-- proof
  apply StatMech.Walls.bgf2_mem_box0_iff

/--
[bgf2_indexAllOpen_zero_of_bff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_indexAllOpen_zero_of_bff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
-- given
  (h : bff_BoxAllOpen ω L) :
-- imply
  bgf2_IndexAllOpen ω L 0 := by
-- proof
  apply StatMech.Walls.bgf2_indexAllOpen_zero_of_bff h

/--
[bgf2_q_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_q_eq_zero_iff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {x : Site 2}
-- given
  (h0 : bgf2_IndexAllOpen ω L 0) :
-- imply
  bgf2_q ω L x = 0 ↔ bgn_idx L x = 0 := by
-- proof
  apply StatMech.Walls.bgf2_q_eq_zero_iff h0

/--
[bgf2_q_eq_zero_iff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_q_eq_zero_iff_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {x : Site 2}
-- given
  (h0 : bgf2_IndexAllOpen ω L 0) :
-- imply
  bgf2_q ω L x = 0 ↔ x ∈ bc61_boxAround 2 L 0 := by
-- proof
  apply StatMech.Walls.bgf2_q_eq_zero_iff_mem h0

/--
[bgf2_indexAllOpen_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_indexAllOpen_cut_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j : Site 2}
-- given
  (h : bgf2_IndexAllOpen ω L j)
  (hj : j ≠ 0) :
-- imply
  bgf2_IndexAllOpen (removeSites (bc61_boxAround 2 L 0) ω) L j := by
-- proof
  apply StatMech.Walls.bgf2_indexAllOpen_cut h hj

/--
[bgf2_cut_q_eq_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_cut_q_eq_connected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {a b : Site 2}
-- given
  (h0 : bgf2_IndexAllOpen ω L 0)
  (h : bgf2_q ω L a = bgf2_q ω L b)
  (hne : bgf2_q ω L a ≠ 0) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) a b := by
-- proof
  apply StatMech.Walls.bgf2_cut_q_eq_connected h0 h hne

/--
[bgf2_cut_connected_of_reach_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_cut_connected_of_reach_aux_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
-- given
  (h0 : bgf2_IndexAllOpen ω L 0) :
-- imply
  ∀ {u v : Site 2}, (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable u v → ∀ a b, bgf2_q ω L a = u → bgf2_q ω L b = v → u ≠ 0 → v ≠ 0 → Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) a b := by
-- proof
  apply StatMech.Walls.bgf2_cut_connected_of_reach_aux h0

/--
[bgf2_trif_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_trif_separation_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
-- given
  (h : bao_AllOpenTrif ω L) :
-- imply
  ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ (0 : Site 2) ∧ w₂ ≠ (0 : Site 2) ∧ w₃ ≠ (0 : Site 2) ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃ := by
-- proof
  apply StatMech.Walls.bgf2_trif_separation h

/--
[bgf2_trif_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_trif_deg3_eq
  [Fintype V]
  {H T : SimpleGraph V}
  [DecidableRel T.Adj]
  {hub w₁ w₂ w₃ : V}
-- given
  (hTH : T ≤ H)
  (hTconn : T.Connected)
  (hne₁ : w₁ ≠ hub)
  (hne₂ : w₂ ≠ hub)
  (hne₃ : w₃ ≠ hub)
  (hs₁₂ : ¬ (bkg_deleteVertex H hub).Reachable w₁ w₂)
  (hs₁₃ : ¬ (bkg_deleteVertex H hub).Reachable w₁ w₃)
  (hs₂₃ : ¬ (bkg_deleteVertex H hub).Reachable w₂ w₃) :
-- imply
  3 ≤ T.degree hub := by
-- proof
  apply StatMech.Walls.bgf2_trif_deg3 hTH hTconn hne₁ hne₂ hne₃ hs₁₂ hs₁₃ hs₂₃

/--
[bgf2_onlyBox0_hub_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_onlyBox0_hub_merged_eq
  {L : ℕ} :
-- imply
  bgf2_IndexAllOpen (bao_onlyBox0 L) L 0 := by
-- proof
  apply StatMech.Walls.bgf2_onlyBox0_hub_merged

/--
[bgf2_onlyBox0_not_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_onlyBox0_not_merged_eq
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  ¬ bgf2_IndexAllOpen (bao_onlyBox0 L) L (bc57_pt 1 0) := by
-- proof
  apply StatMech.Walls.bgf2_onlyBox0_not_merged hL

/--
[bgf2_onlyBox0_not_identified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_onlyBox0_not_identified_eq
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  bgf2_q (bao_onlyBox0 L) L (bc57_pt (2 * (L : ℤ) + 1) 0) ≠ bgf2_q (bao_onlyBox0 L) L (bc57_pt (2 * (L : ℤ) + 1) 1) := by
-- proof
  apply StatMech.Walls.bgf2_onlyBox0_not_identified hL

/--
[bgf2_onlyBox0_box_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_onlyBox0_box_connected_eq
  {L : ℕ}
  {a b : Site 2}
-- given
  (ha : bgn_idx L a = 0)
  (hb : bgn_idx L b = 0) :
-- imply
  Connected 2 (bao_onlyBox0 L) a b := by
-- proof
  apply StatMech.Walls.bgf2_onlyBox0_box_connected ha hb

/--
[bgf2_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean)
-/
@[path]
private lemma bgf2_status_eq :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (a b : Site 2), (bgf2_Gf ω L).Reachable (bgf2_q ω L a) (bgf2_q ω L b) ↔ Connected 2 ω a b) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bao_AllOpenTrif ω L → ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0 ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃) ∧ (∀ (L : ℕ), 1 ≤ L → ¬ bgf2_IndexAllOpen (bao_onlyBox0 L) L (bc57_pt 1 0)) := by
-- proof
  apply StatMech.Walls.bgf2_status


-- created on 2026-10-23
