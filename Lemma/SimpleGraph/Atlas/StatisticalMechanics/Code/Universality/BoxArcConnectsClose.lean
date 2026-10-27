import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[bac_rightComplement_subset_boxMinusL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_rightComplement_subset_boxMinusL_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  bac_rightComplement ω n ⊆ bac_boxMinusL ω n := by
-- proof
  apply StatMech.Universality.bac_rightComplement_subset_boxMinusL ω n

/--
[bac_rightComplement_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_rightComplement_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v : Site 2}
-- given
  (hv : v ∈ bac_rightComplement ω n) :
-- imply
  v ∈ rect 0 n 0 n ∧ v ∉ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.bac_rightComplement_mem ω n hv

/--
[bac_rightWall_mem_rightComplement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_rightWall_mem_rightComplement_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {r : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hr0 : 0 ≤ r)
  (hrn : r ≤ n) :
-- imply
  (![n, r] : Site 2) ∈ bac_rightComplement ω n := by
-- proof
  apply StatMech.Universality.bac_rightWall_mem_rightComplement ω n hnoH hr0 hrn

/--
[bac_rightSegment_notMem_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_rightSegment_notMem_L_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c r : ℤ}
  {c' : ℤ}
-- given
  (htr : mbc_IsRightFrontier ω n c r)
  (hcc' : c < c')
  (hc'n : c' ≤ n) :
-- imply
  (![c', r] : Site 2) ∉ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.bac_rightSegment_notMem_L ω n htr hcc' hc'n

/--
[bac_gap_mem_rightComplement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_gap_mem_rightComplement_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c r : ℤ}
-- given
  (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hr0 : 0 ≤ r)
  (hrn : r ≤ n)
  (htr : mbc_IsRightFrontier ω n c r) :
-- imply
  (![c + 1, r] : Site 2) ∈ bac_rightComplement ω n := by
-- proof
  apply StatMech.Universality.bac_gap_mem_rightComplement ω n _hnoH hr0 hrn htr

/--
[bac_frontierFace_lowerRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_frontierFace_lowerRight_eq
  {c r : ℤ} :
-- imply
  faceCorner10 c r = ![c + 1, r] := by
-- proof
  apply StatMech.Universality.bac_frontierFace_lowerRight c r

/--
[bac_frontierFace_isRCoast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_frontierFace_isRCoast_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c r : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hr0 : 0 ≤ r)
  (hrn : r ≤ n)
  (htr : mbc_IsRightFrontier ω n c r) :
-- imply
  bac_IsRCoastFace ω n ![c, r] := by
-- proof
  apply StatMech.Universality.bac_frontierFace_isRCoast ω n hnoH hr0 hrn htr

/--
[bac_reachesBottom_of_rCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_reachesBottom_of_rCoastConnected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : bac_RCoastConnected ω n) :
-- imply
  ccc_FrontierReachesBottom ω n := by
-- proof
  apply StatMech.Universality.bac_reachesBottom_of_rCoastConnected ω n hn hnoH hres

/--
[bac_frontierArcReaches_of_rCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_frontierArcReaches_of_rCoastConnected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : bac_RCoastConnected ω n) :
-- imply
  crc2_FrontierArcReaches ω n := by
-- proof
  apply StatMech.Universality.bac_frontierArcReaches_of_rCoastConnected ω n hn hnoH hres

/--
[bac_rCoastConnected_of_barrierConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_rCoastConnected_of_barrierConnected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (h : bac_BarrierConnected ω n) :
-- imply
  bac_RCoastConnected ω n := by
-- proof
  apply StatMech.Universality.bac_rCoastConnected_of_barrierConnected ω n hn _hnoH h

/--
[bac_rightComplement_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_rightComplement_connected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v : Site 2}
-- given
  (hv : v ∈ bac_rightComplement ω n) :
-- imply
  ∃ (y : Site 2) (_hy : y ∈ rightSide 0 n 0 n) (hvc : v ∈ bac_boxMinusL ω n) (hyc : y ∈ bac_boxMinusL ω n), ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨v, hvc⟩ ⟨y, hyc⟩ := by
-- proof
  apply StatMech.Universality.bac_rightComplement_connected ω n hv

/--
[bac_faceDualVCrossing_of_rCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_faceDualVCrossing_of_rCoastConnected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : bac_RCoastConnected ω n) :
-- imply
  pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.bac_faceDualVCrossing_of_rCoastConnected ω n hn hnoH hres

/--
[bac_exhaustivity_of_rCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_exhaustivity_of_rCoastConnected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : bac_RCoastConnected ω n) :
-- imply
  HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.bac_exhaustivity_of_rCoastConnected ω n hn hnoH hres

/--
[bac_wall_leftReach_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_leftReach_iff_eq
  {v : Site 2}
-- given
  (hv : v ∈ rect 0 2 0 2) :
-- imply
  v ∈ bcd_leftReach bcc_wallCfg 2 ↔ v 0 = 0 := by
-- proof
  apply StatMech.Universality.bac_wall_leftReach_iff hv

/--
[bac_wall_face_from_horiz_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_face_from_horiz_edge_eq
  {f g : Site 2}
  {c : ℤ}
-- given
  (hadj : (hypercubicLattice 2).Adj f g)
  (hedge : sharedPrimalEdge f g = s(![0, c], ![1, c])) :
-- imply
  f 0 = 0 ∧ (f 1 = c ∨ f 1 = c - 1) := by
-- proof
  apply StatMech.Universality.bac_wall_face_from_horiz_edge hadj hedge

/--
[bac_wall_barrierFace_col0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_barrierFace_col0_eq
  {f g : Site 2}
-- given
  (h : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj f g) :
-- imply
  f 0 = 0 ∧ (f 1 = -1 ∨ f 1 = 0 ∨ f 1 = 1 ∨ f 1 = 2) := by
-- proof
  apply StatMech.Universality.bac_wall_barrierFace_col0 h

/--
[bac_wall_col0_reaches_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_col0_reaches_origin_eq
  {b : ℤ}
-- given
  (hb : b = -1 ∨ b = 0 ∨ b = 1 ∨ b = 2) :
-- imply
  (pmd_boxFaceBarrier bcc_wallCfg 2).Reachable ![0, b] ![0, 0] := by
-- proof
  apply StatMech.Universality.bac_wall_col0_reaches_origin hb

/--
[bac_wall_rCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_rCoastConnected_eq :
-- imply
  bac_RCoastConnected bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.bac_wall_rCoastConnected

/--
[bac_wall_frontierArcReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_frontierArcReaches_eq :
-- imply
  crc2_FrontierArcReaches bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.bac_wall_frontierArcReaches

/--
[bac_wall_reachesBottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_reachesBottom_eq :
-- imply
  ccc_FrontierReachesBottom bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.bac_wall_reachesBottom

/--
[bac_wall_faceDualVCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_faceDualVCrossing_eq :
-- imply
  pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.bac_wall_faceDualVCrossing

/--
[bac_wall_gap_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_gap_mem_eq :
-- imply
  (![1, 0] : Site 2) ∈ bac_rightComplement bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.bac_wall_gap_mem

/--
[bac_wall_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean)
-/
@[path]
private lemma bac_wall_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.bac_wall_noH


-- created on 2026-10-23
