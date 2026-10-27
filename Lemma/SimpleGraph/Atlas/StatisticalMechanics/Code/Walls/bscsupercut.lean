import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bscsupercut.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bsc_ediv_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_ediv_zero_iff_eq
  {d : ℕ}
  {L : ℕ}
  {a : ℤ} :
-- imply
  (a + (L : ℤ)) / (2 * (L : ℤ) + 1) = 0 ↔ a.natAbs ≤ L := by
-- proof
  apply StatMech.Walls.bsc_ediv_zero_iff

/--
[bsc_boxCentre_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_boxCentre_zero_eq
  {d : ℕ}
  {d L : ℕ} :
-- imply
  bsc_IsBoxCentre L (0 : Site d) := by
-- proof
  apply StatMech.Walls.bsc_boxCentre_zero d L

/--
[bsc_box_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_box_isolated_eq
  {d : ℕ}
  {L : ℕ}
  {y a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : Site d}
-- given
  (ha : a ∈ bc61_boxAround d L y) :
-- imply
  ¬ (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj a w := by
-- proof
  apply StatMech.Walls.bsc_box_isolated ω ha w

/--
[bsc_notMem_box_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_notMem_box_of_infinite_eq
  {d : ℕ}
  {L : ℕ}
  {y a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  a ∉ bc61_boxAround d L y := by
-- proof
  apply StatMech.Walls.bsc_notMem_box_of_infinite hinf

/--
[bsc_hub_adj_armImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_hub_adj_armImage_eq
  {d : ℕ}
  {L : ℕ}
  {y a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hy : bsc_IsBoxCentre L y)
  (hinc : bc67_GnIncident ω L y a)
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  bgn_idx L a ≠ bgn_idx L y ∧ (bgn_Gn ω L).Adj (bgn_idx L y) (bgn_idx L a) := by
-- proof
  apply StatMech.Walls.bsc_hub_adj_armImage hy hinc hinf

/--
[bsc_superReach_of_siteConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_superReach_of_siteConn_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (hy : bsc_IsBoxCentre L y)
  (h : Connected d (removeSites (bc61_boxAround d L y) ω) a b) :
-- imply
  (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable (bgn_idx L a) (bgn_idx L b) := by
-- proof
  apply StatMech.Walls.bsc_superReach_of_siteConn hy h

/--
[bsc_ediv_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_ediv_eq_iff_eq
  {d : ℕ}
  {L : ℕ}
  {a m : ℤ} :
-- imply
  (a + (L : ℤ)) / (2 * (L : ℤ) + 1) = m ↔ (a - (2 * (L : ℤ) + 1) * m).natAbs ≤ L := by
-- proof
  apply StatMech.Walls.bsc_ediv_eq_iff

/--
[bsc_fiber_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_fiber_finite_eq
  {d : ℕ}
  {L : ℕ}
  {j : Site d} :
-- imply
  {x : Site d | bgn_idx L x = j}.Finite := by
-- proof
  apply StatMech.Walls.bsc_fiber_finite L j

/--
[bsc_deleteWalk_support_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_deleteWalk_support_avoid_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {t : V} :
-- imply
  ∀ {u v : V} (p : (bkg_deleteVertex G t).Walk u v), u ≠ t → t ∉ p.support := by
-- proof
  apply StatMech.Walls.bsc_deleteWalk_support_avoid

/--
[bsc_ray34_of_deleteReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_ray34_of_deleteReach_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {t u v : V}
-- given
  (hu : u ≠ t)
  (h : (bkg_deleteVertex G t).Reachable u v) :
-- imply
  ray34_AvoidReach G {t} u v := by
-- proof
  apply StatMech.Walls.bsc_ray34_of_deleteReach hu h

/--
[bsc_arm_ray_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_arm_ray_infinite_eq
  {d : ℕ}
  {L : ℕ}
  {y a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hy : bsc_IsBoxCentre L y)
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} (bgn_idx L a)).Infinite := by
-- proof
  apply StatMech.Walls.bsc_arm_ray_infinite hy hinf

/--
[bsc_siteConn_of_superReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_siteConn_of_superReach_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (hy : bsc_IsBoxCentre L y)
  (hint : bsc_BoxesInternallyConnected ω L y)
  (ha : bgn_idx L a ≠ bgn_idx L y)
  (hb : bgn_idx L b ≠ bgn_idx L y)
  (h : (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable (bgn_idx L a) (bgn_idx L b)) :
-- imply
  Connected d (removeSites (bc61_boxAround d L y) ω) a b := by
-- proof
  apply StatMech.Walls.bsc_siteConn_of_superReach hy hint ha hb h

/--
[bsc_super_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_super_disconnected_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (hy : bsc_IsBoxCentre L y)
  (hint : bsc_BoxesInternallyConnected ω L y)
  (ha : bgn_idx L a ≠ bgn_idx L y)
  (hb : bgn_idx L b ≠ bgn_idx L y)
  (hdis : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a b) :
-- imply
  ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable (bgn_idx L a) (bgn_idx L b) := by
-- proof
  apply StatMech.Walls.bsc_super_disconnected hy hint ha hb hdis

/--
[bsc_bridge_of_internalConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_bridge_of_internalConn_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hy : bsc_IsBoxCentre L y)
  (hint : bsc_BoxesInternallyConnected ω L y)
  (htri : bc67_IsGnTrifurcation ω L y) :
-- imply
  ∃ w₁ w₂ w₃ : Site d, w₁ ≠ bgn_idx L y ∧ w₂ ≠ bgn_idx L y ∧ w₃ ≠ bgn_idx L y ∧ (bgn_Gn ω L).Adj (bgn_idx L y) w₁ ∧ (bgn_Gn ω L).Adj (bgn_idx L y) w₂ ∧ (bgn_Gn ω L).Adj (bgn_idx L y) w₃ ∧ ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₂ ∧ ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₃ ∧ ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₂ w₃ ∧ (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₁).Infinite ∧ (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₂).Infinite ∧ (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₃).Infinite := by
-- proof
  apply StatMech.Walls.bsc_bridge_of_internalConn hy hint htri

/--
[bsc_bfin_SuperCutBridge_of_hyp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_bfin_SuperCutBridge_of_hyp_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
-- given
  (H : ∀ y : Site 2, bc67_IsGnTrifurcation ω L y → bsc_IsBoxCentre L y ∧ bsc_BoxesInternallyConnected ω L y) :
-- imply
  bfin_SuperCutBridge ω L := by
-- proof
  apply StatMech.Walls.bsc_bfin_SuperCutBridge_of_hyp ω L H

/--
[bsc_upperLines_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_upperLines_forward_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ w₁ w₂ w₃ : Site 2, (w₁ ≠ bgn_idx L (0 : Site 2) ∧ w₂ ≠ bgn_idx L (0 : Site 2) ∧ w₃ ≠ bgn_idx L (0 : Site 2)) ∧ ((bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₁ ∧ (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₂ ∧ (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₃) ∧ ((ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₁).Infinite ∧ (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₂).Infinite ∧ (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₃).Infinite) := by
-- proof
  apply StatMech.Walls.bsc_upperLines_forward hL

/--
[bsc_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean)
-/
@[path]
private lemma bsc_status_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  (∃ w₁ w₂ w₃ : Site 2, (w₁ ≠ bgn_idx L (0 : Site 2) ∧ w₂ ≠ bgn_idx L (0 : Site 2) ∧ w₃ ≠ bgn_idx L (0 : Site 2)) ∧ ((bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₁ ∧ (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₂ ∧ (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₃) ∧ ((ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₁).Infinite ∧ (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₂).Infinite ∧ (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₃).Infinite)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))), (∀ y : Site 2, bc67_IsGnTrifurcation ω L y → bsc_IsBoxCentre L y ∧ bsc_BoxesInternallyConnected ω L y) → bfin_SuperCutBridge ω L) := by
-- proof
  apply StatMech.Walls.bsc_status hL


-- created on 2026-10-23
