import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[ccc_frontierFace_down_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_frontierFace_down_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c r : ℤ}
-- given
  (hr0 : 0 ≤ r)
  (hrn : r ≤ n)
  (htr : mbc_IsRightFrontier ω n c r) :
-- imply
  (pmd_boxFaceBarrier ω n).Adj ![c, r] ![c, r - 1] := by
-- proof
  apply StatMech.Universality.ccc_frontierFace_down_adj ω n hr0 hrn htr

/--
[ccc_rightFrontier_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_rightFrontier_unique_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c c' r : ℤ}
-- given
  (hc : mbc_IsRightFrontier ω n c r)
  (hc' : mbc_IsRightFrontier ω n c' r) :
-- imply
  c = c' := by
-- proof
  apply StatMech.Universality.ccc_rightFrontier_unique ω n hc hc'

/--
[ccc_frontierRungsConnect_of_reachesBottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_frontierRungsConnect_of_reachesBottom_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hatom : ccc_FrontierReachesBottom ω n) :
-- imply
  mbc_FrontierRungsConnect ω n := by
-- proof
  apply StatMech.Universality.ccc_frontierRungsConnect_of_reachesBottom ω n hatom

/--
[ccc_reachesAnchor_of_frontierRungsConnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_reachesAnchor_of_frontierRungsConnect_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : mbc_FrontierRungsConnect ω n) :
-- imply
  ccc_FrontierReachesBottom ω n := by
-- proof
  apply StatMech.Universality.ccc_reachesAnchor_of_frontierRungsConnect ω n hn hnoH hres

/--
[ccc_barrierConnectsRows_of_reachesBottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_barrierConnectsRows_of_reachesBottom_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hatom : ccc_FrontierReachesBottom ω n) :
-- imply
  pmd_BarrierConnectsRows ω n := by
-- proof
  apply StatMech.Universality.ccc_barrierConnectsRows_of_reachesBottom ω n hn hnoH hatom

/--
[ccc_faceDualVCrossing_of_reachesBottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_faceDualVCrossing_of_reachesBottom_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hatom : ccc_FrontierReachesBottom ω n) :
-- imply
  pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.ccc_faceDualVCrossing_of_reachesBottom ω n hn hnoH hatom

/--
[ccc_exhaustivity_of_reachesBottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_exhaustivity_of_reachesBottom_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hatom : ccc_FrontierReachesBottom ω n) :
-- imply
  HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.ccc_exhaustivity_of_reachesBottom ω n hn hnoH hatom

/--
[ccc_wall_bottom_rung](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_wall_bottom_rung_eq :
-- imply
  (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ)] ![0, (0 : ℤ) - 1] := by
-- proof
  apply StatMech.Universality.ccc_wall_bottom_rung

/--
[ccc_wall_frontierReachesBottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_wall_frontierReachesBottom_eq :
-- imply
  ccc_FrontierReachesBottom bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.ccc_wall_frontierReachesBottom

/--
[ccc_wall_frontierRungsConnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_wall_frontierRungsConnect_eq :
-- imply
  mbc_FrontierRungsConnect bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.ccc_wall_frontierRungsConnect

/--
[ccc_wall_barrierConnectsRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_wall_barrierConnectsRows_eq :
-- imply
  pmd_BarrierConnectsRows bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.ccc_wall_barrierConnectsRows

/--
[ccc_wall_faceDualVCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_wall_faceDualVCrossing_eq :
-- imply
  pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.ccc_wall_faceDualVCrossing

/--
[ccc_wall_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean)
-/
@[path]
private lemma ccc_wall_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.ccc_wall_noH


-- created on 2026-10-23
