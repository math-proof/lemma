import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[mbc_rightFrontier_succ_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_rightFrontier_succ_notMem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n c r : ℤ}
-- given
  (h : mbc_IsRightFrontier ω n c r) :
-- imply
  (![c + 1, r] : Site 2) ∉ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.mbc_rightFrontier_succ_notMem ω n c r h

/--
[mbc_exists_rightFrontier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_exists_rightFrontier_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {r : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hr0 : 0 ≤ r)
  (hrn : r ≤ n) :
-- imply
  ∃ c : ℤ, mbc_IsRightFrontier ω n c r := by
-- proof
  apply StatMech.Universality.mbc_exists_rightFrontier ω n hn hnoH hr0 hrn

/--
[mbc_rung_vAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_rung_vAdj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c r : ℤ}
-- given
  (hr0 : 0 ≤ r)
  (hrn : r ≤ n)
  (htr : mbc_IsRightFrontier ω n c r) :
-- imply
  (pmd_boxFaceBarrier ω n).Adj ![c, r - 1] ![c, r] := by
-- proof
  apply StatMech.Universality.mbc_rung_vAdj ω n hr0 hrn htr

/--
[mbc_reach_to_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_reach_to_row_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c0 : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : mbc_FrontierRungsConnect ω n)
  (h0 : mbc_IsRightFrontier ω n c0 0) :
-- imply
  ∀ (k : ℕ), (k : ℤ) ≤ n → ∃ ck : ℤ, mbc_IsRightFrontier ω n ck (k : ℤ) ∧ (pmd_boxFaceBarrier ω n).Reachable ![c0, -1] ![ck, (k : ℤ)] := by
-- proof
  apply StatMech.Universality.mbc_reach_to_row ω n hn hnoH hres h0

/--
[mbc_barrierConnectsRows_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_barrierConnectsRows_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : mbc_FrontierRungsConnect ω n) :
-- imply
  pmd_BarrierConnectsRows ω n := by
-- proof
  apply StatMech.Universality.mbc_barrierConnectsRows_of_residue ω n hn hnoH hres

/--
[mbc_faceDualVCrossing_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_faceDualVCrossing_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : mbc_FrontierRungsConnect ω n) :
-- imply
  pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.mbc_faceDualVCrossing_of_residue ω n hn hnoH hres

/--
[mbc_exhaustivity_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_exhaustivity_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : mbc_FrontierRungsConnect ω n) :
-- imply
  HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.mbc_exhaustivity_of_residue ω n hn hnoH hres

/--
[mbc_wall_rightFrontier_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_wall_rightFrontier_zero_eq
  {c r : ℤ}
-- given
  (h : mbc_IsRightFrontier bcc_wallCfg 2 c r) :
-- imply
  c = 0 := by
-- proof
  apply StatMech.Universality.mbc_wall_rightFrontier_zero h

/--
[mbc_wall_frontierRungsConnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_wall_frontierRungsConnect_eq :
-- imply
  mbc_FrontierRungsConnect bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.mbc_wall_frontierRungsConnect

/--
[mbc_wall_barrierConnectsRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_wall_barrierConnectsRows_eq :
-- imply
  pmd_BarrierConnectsRows bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.mbc_wall_barrierConnectsRows

/--
[mbc_wall_faceDualVCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_wall_faceDualVCrossing_eq :
-- imply
  pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.mbc_wall_faceDualVCrossing

/--
[mbc_residue_atom_single_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_residue_atom_single_step_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n r c c' : ℤ}
-- given
  (h : c = c') :
-- imply
  (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c', r] := by
-- proof
  apply StatMech.Universality.mbc_residue_atom_single_step ω n r c c' h

/--
[mbc_wall_rightFrontier_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_wall_rightFrontier_at_eq
  {r : ℤ}
-- given
  (hr0 : 0 ≤ r)
  (hr2 : r ≤ 2) :
-- imply
  mbc_IsRightFrontier bcc_wallCfg 2 0 r := by
-- proof
  apply StatMech.Universality.mbc_wall_rightFrontier_at hr0 hr2

/--
[mbc_wall_bottom_rung_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_wall_bottom_rung_real_eq :
-- imply
  (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ) - 1] ![0, (0 : ℤ)] := by
-- proof
  apply StatMech.Universality.mbc_wall_bottom_rung_real

/--
[mbc_wall_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean)
-/
@[path]
private lemma mbc_wall_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.mbc_wall_noH


-- created on 2026-10-23
