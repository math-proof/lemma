import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.CoastlineAnchorClose
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[cac_boxFaceBarrier_le_faceBoundaryGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_boxFaceBarrier_le_faceBoundaryGraph_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  pmd_boxFaceBarrier ω n ≤ faceBoundaryGraph (bcd_leftReach ω n) := by
-- proof
  apply StatMech.Universality.cac_boxFaceBarrier_le_faceBoundaryGraph ω n

/--
[cac_barrier_reach_lifts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_barrier_reach_lifts_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g : Site 2}
-- given
  (h : (pmd_boxFaceBarrier ω n).Reachable f g) :
-- imply
  (faceBoundaryGraph (bcd_leftReach ω n)).Reachable f g := by
-- proof
  apply StatMech.Universality.cac_barrier_reach_lifts ω n h

/--
[cac_dualCircuit_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_dualCircuit_exists_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hc0 : 0 ≤ c)
  (hcn : c ≤ n) :
-- imply
  ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), cyc.IsCycle := by
-- proof
  apply StatMech.Universality.cac_dualCircuit_exists ω hn hnoH hc0 hcn

/--
[cac_frontierReachesBottom_of_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_frontierReachesBottom_of_anchor_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a₀ b₀ : ℤ}
-- given
  (ha0 : 0 ≤ a₀)
  (ha0' : a₀ ≤ n - 1)
  (hb0 : -1 ≤ b₀)
  (hb0' : b₀ ≤ n)
  (h : cac_AllFrontierReachAnchor ω n a₀ b₀) :
-- imply
  ccc_FrontierReachesBottom ω n := by
-- proof
  apply StatMech.Universality.cac_frontierReachesBottom_of_anchor ω n ha0 ha0' hb0 hb0' h

/--
[cac_row0_frontier_reaches_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_row0_frontier_reaches_bottom_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c₀ : ℤ}
-- given
  (hn : 0 ≤ n)
  (h0 : mbc_IsRightFrontier ω n c₀ 0) :
-- imply
  (pmd_boxFaceBarrier ω n).Reachable ![c₀, 0] ![c₀, -1] := by
-- proof
  apply StatMech.Universality.cac_row0_frontier_reaches_bottom ω n hn h0

/--
[cac_anchor_in_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_anchor_in_range_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c₀ : ℤ}
-- given
  (hn : 0 ≤ n)
  (h0 : mbc_IsRightFrontier ω n c₀ 0) :
-- imply
  0 ≤ c₀ ∧ c₀ ≤ n - 1 ∧ (-1 : ℤ) ≤ -1 ∧ (-1 : ℤ) ≤ n := by
-- proof
  apply StatMech.Universality.cac_anchor_in_range ω n hn h0

/--
[cac_atom_of_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_atom_of_pinned_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (h : cac_FrontierReachesBottomAtAnchor ω n) :
-- imply
  ccc_FrontierReachesBottom ω n := by
-- proof
  apply StatMech.Universality.cac_atom_of_pinned ω n hn hnoH h

/--
[cac_pinned_of_atom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_pinned_of_atom_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (h : ccc_FrontierReachesBottom ω n) :
-- imply
  cac_FrontierReachesBottomAtAnchor ω n := by
-- proof
  apply StatMech.Universality.cac_pinned_of_atom ω n hn h

/--
[cac_wall_frontierReachesBottomAtAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_wall_frontierReachesBottomAtAnchor_eq :
-- imply
  cac_FrontierReachesBottomAtAnchor bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.cac_wall_frontierReachesBottomAtAnchor

/--
[cac_wall_atom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_wall_atom_eq :
-- imply
  ccc_FrontierReachesBottom bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.cac_wall_atom

/--
[cac_wall_faceDualVCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_wall_faceDualVCrossing_eq :
-- imply
  pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.cac_wall_faceDualVCrossing

/--
[cac_wall_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean)
-/
@[path]
private lemma cac_wall_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.cac_wall_noH


-- created on 2026-10-23
