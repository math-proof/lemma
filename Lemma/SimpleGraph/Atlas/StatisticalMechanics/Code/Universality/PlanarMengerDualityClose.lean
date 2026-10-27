import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[pmd_faceVAdj_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_faceVAdj_of_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b : ℤ}
-- given
  (hcl : ω s(![a, b + 1], ![a + 1, b + 1]) = false) :
-- imply
  (fci_faceOpenDual ω).Adj ![a, b] ![a, b + 1] := by
-- proof
  apply StatMech.Universality.pmd_faceVAdj_of_closed ω a b hcl

/--
[pmd_faceHAdj_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_faceHAdj_of_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b : ℤ}
-- given
  (hcl : ω s(![a + 1, b], ![a + 1, b + 1]) = false) :
-- imply
  (fci_faceOpenDual ω).Adj ![a, b] ![a + 1, b] := by
-- proof
  apply StatMech.Universality.pmd_faceHAdj_of_closed ω a b hcl

/--
[pmd_faceDualVCrossing_of_spanningContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_faceDualVCrossing_of_spanningContour_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {u : Site 2}
  {c : (fci_faceOpenDual ω).Walk u u}
  {a₀ a₁ : ℤ}
-- given
  (ha0 : 0 ≤ a₀)
  (ha0' : a₀ ≤ n - 1)
  (ha1 : 0 ≤ a₁)
  (ha1' : a₁ ≤ n - 1)
  (hbot : (![a₀, -1] : Site 2) ∈ c.support)
  (htop : (![a₁, n] : Site 2) ∈ c.support) :
-- imply
  pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.pmd_faceDualVCrossing_of_spanningContour ω n c ha0 ha0' ha1 ha1' hbot htop

/--
[pmd_faceDualV_implies_spanningReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_faceDualV_implies_spanningReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : pmd_FaceDualVCrossing ω n) :
-- imply
  ∃ (a₀ a₁ : ℤ), (fci_faceOpenDual ω).Reachable ![a₀, -1] ![a₁, n] := by
-- proof
  apply StatMech.Universality.pmd_faceDualV_implies_spanningReach ω n h

/--
[pmd_boxFaceBarrier_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_boxFaceBarrier_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g : Site 2} :
-- imply
  (pmd_boxFaceBarrier ω n).Adj f g ↔ (hypercubicLattice 2).Adj f g ∧ ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ bdEdge (bcd_leftReach ω n) s(p, q) ∧ p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n := by
-- proof
  apply StatMech.Universality.pmd_boxFaceBarrier_adj ω n f g

/--
[pmd_boxFaceBarrier_le_faceOpenDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_boxFaceBarrier_le_faceOpenDual_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  pmd_boxFaceBarrier ω n ≤ fci_faceOpenDual ω := by
-- proof
  apply StatMech.Universality.pmd_boxFaceBarrier_le_faceOpenDual ω n

/--
[pmd_faceDualVCrossing_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_faceDualVCrossing_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : pmd_BarrierConnectsRows ω n) :
-- imply
  pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.pmd_faceDualVCrossing_of_residue ω n h

/--
[pmd_contour_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_contour_exists_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.pmd_contour_exists ω n hn hnoH

/--
[pmd_exhaustivity_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_exhaustivity_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (h : pmd_BarrierConnectsRows ω n) :
-- imply
  HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.pmd_exhaustivity_of_residue ω n _hnoH h

/--
[pmd_wall_faceVAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_wall_faceVAdj_eq
  {b : ℤ}
-- given
  (hb : b = -1 ∨ b = 0 ∨ b = 1) :
-- imply
  (fci_faceOpenDual bcc_wallCfg).Adj ![0, b] ![0, b + 1] := by
-- proof
  apply StatMech.Universality.pmd_wall_faceVAdj hb

/--
[pmd_wall_faceDualVCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_wall_faceDualVCrossing_eq :
-- imply
  pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.pmd_wall_faceDualVCrossing

/--
[pmd_wall_barrierVAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_wall_barrierVAdj_eq
  {b : ℤ}
-- given
  (hb : b = -1 ∨ b = 0 ∨ b = 1) :
-- imply
  (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, b] ![0, b + 1] := by
-- proof
  apply StatMech.Universality.pmd_wall_barrierVAdj hb

/--
[pmd_wall_barrierConnectsRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_wall_barrierConnectsRows_eq :
-- imply
  pmd_BarrierConnectsRows bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.pmd_wall_barrierConnectsRows

/--
[pmd_wall_faceDualV_via_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_wall_faceDualV_via_residue_eq :
-- imply
  pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.pmd_wall_faceDualV_via_residue

/--
[pmd_wall_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_wall_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.pmd_wall_noH

/--
[pmd_wall_noH_yet_faceDualV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_wall_noH_yet_faceDualV_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.pmd_wall_noH_yet_faceDualV

/--
[pmd_wall_only_face_frame_works](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean)
-/
@[path]
private lemma pmd_wall_only_face_frame_works_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ jex_DualBarrierVCrossing bcc_wallCfg 2 ∧ ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 ∧ pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.pmd_wall_only_face_frame_works


-- created on 2026-10-23
