import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RCoastMengerClose
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[rcm_horizEdge_faces_pmdAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_horizEdge_faces_pmdAdj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : ℤ}
-- given
  (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x + 1, y]))
  (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n)
  (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
-- imply
  (pmd_boxFaceBarrier ω n).Adj ![x, y] ![x, y - 1] := by
-- proof
  apply StatMech.Universality.rcm_horizEdge_faces_pmdAdj ω n hbd hp hq

/--
[rcm_vertEdge_faces_pmdAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_vertEdge_faces_pmdAdj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : ℤ}
-- given
  (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x, y + 1]))
  (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n)
  (hq : (![x, y + 1] : Site 2) ∈ rect 0 n 0 n) :
-- imply
  (pmd_boxFaceBarrier ω n).Adj ![x, y] ![x - 1, y] := by
-- proof
  apply StatMech.Universality.rcm_vertEdge_faces_pmdAdj ω n hbd hp hq

/--
[rcm_LR_edge_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_LR_edge_bdEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (hpL : p ∈ bcd_leftReach ω n)
  (hqR : q ∈ bac_rightComplement ω n) :
-- imply
  bdEdge (bcd_leftReach ω n) s(p, q) := by
-- proof
  apply StatMech.Universality.rcm_LR_edge_bdEdge ω n hpL hqR

/--
[rcm_LR_horizEdge_faces_pmdAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_LR_horizEdge_faces_pmdAdj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : ℤ}
-- given
  (hpL : (![x, y] : Site 2) ∈ bcd_leftReach ω n)
  (hqR : (![x + 1, y] : Site 2) ∈ bac_rightComplement ω n)
  (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n)
  (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
-- imply
  (pmd_boxFaceBarrier ω n).Adj ![x, y] ![x, y - 1] := by
-- proof
  apply StatMech.Universality.rcm_LR_horizEdge_faces_pmdAdj ω n hpL hqR hp hq

/--
[rcm_rightWall_reaches_in_boxMinusL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_rightWall_reaches_in_boxMinusL_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {t : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (ht0 : 0 ≤ t)
  (htn : t ≤ n) :
-- imply
  ∃ (h0 : (![n, 0] : Site 2) ∈ bac_boxMinusL ω n) (ht : (![n, t] : Site 2) ∈ bac_boxMinusL ω n), ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨![n, 0], h0⟩ ⟨![n, t], ht⟩ := by
-- proof
  apply StatMech.Universality.rcm_rightWall_reaches_in_boxMinusL ω n hnoH ht0 htn

/--
[rcm_rightComplement_reaches_rightWall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_rightComplement_reaches_rightWall_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hv : v ∈ bac_rightComplement ω n) :
-- imply
  ∃ (hvc : v ∈ bac_boxMinusL ω n) (h0 : (![n, 0] : Site 2) ∈ bac_boxMinusL ω n), ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨v, hvc⟩ ⟨![n, 0], h0⟩ := by
-- proof
  apply StatMech.Universality.rcm_rightComplement_reaches_rightWall ω n hnoH hv

/--
[rcm_rightComplement_connected_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_rightComplement_connected_pair_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {u v : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hu : u ∈ bac_rightComplement ω n)
  (hv : v ∈ bac_rightComplement ω n) :
-- imply
  ∃ (huc : u ∈ bac_boxMinusL ω n) (hvc : v ∈ bac_boxMinusL ω n), ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨u, huc⟩ ⟨v, hvc⟩ := by
-- proof
  apply StatMech.Universality.rcm_rightComplement_connected_pair ω n hnoH hu hv

/--
[rcm_rCoastConnected_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_rCoastConnected_of_all_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hall : rcm_RCoastConnectedAll ω n) :
-- imply
  bac_RCoastConnected ω n := by
-- proof
  apply StatMech.Universality.rcm_rCoastConnected_of_all ω n hnoH hall

/--
[rcm_all_of_rCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_all_of_rCoastConnected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : bac_RCoastConnected ω n) :
-- imply
  rcm_RCoastConnectedAll ω n := by
-- proof
  apply StatMech.Universality.rcm_all_of_rCoastConnected ω n hn hnoH hres

/--
[rcm_reachesBottom_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_reachesBottom_of_all_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hall : rcm_RCoastConnectedAll ω n) :
-- imply
  ccc_FrontierReachesBottom ω n := by
-- proof
  apply StatMech.Universality.rcm_reachesBottom_of_all ω n hn hnoH hall

/--
[rcm_frontierArcReaches_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_frontierArcReaches_of_all_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hall : rcm_RCoastConnectedAll ω n) :
-- imply
  crc2_FrontierArcReaches ω n := by
-- proof
  apply StatMech.Universality.rcm_frontierArcReaches_of_all ω n hn hnoH hall

/--
[rcm_faceDualVCrossing_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_faceDualVCrossing_of_all_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hall : rcm_RCoastConnectedAll ω n) :
-- imply
  pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.rcm_faceDualVCrossing_of_all ω n hn hnoH hall

/--
[rcm_exhaustivity_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_exhaustivity_of_all_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hall : rcm_RCoastConnectedAll ω n) :
-- imply
  HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.rcm_exhaustivity_of_all ω n hn hnoH hall

/--
[rcm_wall_RCoastConnectedAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_wall_RCoastConnectedAll_eq :
-- imply
  rcm_RCoastConnectedAll bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.rcm_wall_RCoastConnectedAll

/--
[rcm_wall_frontierArcReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_wall_frontierArcReaches_eq :
-- imply
  crc2_FrontierArcReaches bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.rcm_wall_frontierArcReaches

/--
[rcm_wall_faceDualVCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_wall_faceDualVCrossing_eq :
-- imply
  pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.rcm_wall_faceDualVCrossing

/--
[rcm_wall_rightComplement_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_wall_rightComplement_connected_eq :
-- imply
  ∃ (huc : (![1, 0] : Site 2) ∈ bac_boxMinusL bcc_wallCfg 2) (hvc : (![2, 0] : Site 2) ∈ bac_boxMinusL bcc_wallCfg 2), ((hypercubicLattice 2).induce (bac_boxMinusL bcc_wallCfg 2)).Reachable ⟨![1, 0], huc⟩ ⟨![2, 0], hvc⟩ := by
-- proof
  apply StatMech.Universality.rcm_wall_rightComplement_connected

/--
[rcm_wall_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean)
-/
@[path]
private lemma rcm_wall_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.rcm_wall_noH


-- created on 2026-10-23
