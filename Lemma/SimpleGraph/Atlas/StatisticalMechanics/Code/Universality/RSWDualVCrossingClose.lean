import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[rdv_box_frame_target_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_box_frame_target_false_eq :
-- imply
  ¬ (∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 2 0 2 → DualVerticalCrossing ω 0 2 0 2) := by
-- proof
  apply StatMech.Universality.rdv_box_frame_target_false

/--
[rdv_jex_dualBarrierVCrossing_unprovable_from_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_jex_dualBarrierVCrossing_unprovable_from_noH_eq :
-- imply
  ¬ (∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 2 0 2 → jex_DualBarrierVCrossing ω 2) := by
-- proof
  apply StatMech.Universality.rdv_jex_dualBarrierVCrossing_unprovable_from_noH

/--
[rdv_witness_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_witness_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.rdv_witness_noH

/--
[rdv_witness_no_boxFrame_dualV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_witness_no_boxFrame_dualV_eq :
-- imply
  ¬ jex_DualBarrierVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.rdv_witness_no_boxFrame_dualV

/--
[rdv_leftReach_wall_x0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_leftReach_wall_x0_eq
  {v : Site 2}
-- given
  (h : v ∈ bcd_leftReach bcc_wallCfg 2) :
-- imply
  v 0 = 0 := by
-- proof
  apply StatMech.Universality.rdv_leftReach_wall_x0 h

/--
[rdv_barrier_wall_snd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_barrier_wall_snd_le_eq
  {p q : Site 2}
-- given
  (h : (dcw_dualBarrierGraph bcc_wallCfg 2).Adj p q) :
-- imply
  p 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.rdv_barrier_wall_snd_le h

/--
[rdv_barrier_wall_walk_snd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_barrier_wall_walk_snd_le_eq
  {p q : Site 2}
  {c : (dcw_dualBarrierGraph bcc_wallCfg 2).Walk p q}
-- given
  (hp : p 1 ≤ 1) :
-- imply
  q 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.rdv_barrier_wall_walk_snd_le c hp

/--
[rdv_rotResidue_false_on_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_rotResidue_false_on_noH_eq :
-- imply
  ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.rdv_rotResidue_false_on_noH

/--
[rdv_rotated_dualVerticalCrossing_of_rotResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_rotated_dualVerticalCrossing_of_rotResidue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : dcp_DualCutConnectsRot ω n) :
-- imply
  DualVerticalCrossing ω (-n) 0 0 n := by
-- proof
  apply StatMech.Universality.rdv_rotated_dualVerticalCrossing_of_rotResidue ω n h

/--
[rdv_exists_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_exists_dualCircuit_eq
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
  apply StatMech.Universality.rdv_exists_dualCircuit ω hn hnoH hc0 hcn

/--
[rdv_face_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_face_dualCircuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.rdv_face_dualCircuit ω n hn hnoH

/--
[rdv_faceOpenDual_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_faceOpenDual_cycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.rdv_faceOpenDual_cycle ω n hn hnoH

/--
[rdv_face_dualCircuit_edge_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_face_dualCircuit_edge_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g : Site 2}
  {p q : Site 2}
-- given
  (hadj : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpadj : (hypercubicLattice 2).Adj p q)
  (hpbox : p ∈ rect 0 n 0 n)
  (hqbox : q ∈ rect 0 n 0 n) :
-- imply
  dualConfig ω (crossEdge s(p, q)) = true := by
-- proof
  apply StatMech.Universality.rdv_face_dualCircuit_edge_dual_open ω n hadj hpq hpadj hpbox hqbox

/--
[rdv_face_contour_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_face_contour_nonempty_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g := by
-- proof
  apply StatMech.Universality.rdv_face_contour_nonempty ω n hn hnoH

/--
[rdv_no_frameReconcile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_no_frameReconcile_eq :
-- imply
  ¬ ∃ Φ : Site 2 → Site 2, rdv_FrameReconcile Φ := by
-- proof
  apply StatMech.Universality.rdv_no_frameReconcile

/--
[rdv_no_frameChangeIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_no_frameChangeIso_eq :
-- imply
  ¬ ∃ Φ : Site 2 → Site 2, fci_FrameCompat Φ := by
-- proof
  apply StatMech.Universality.rdv_no_frameChangeIso

/--
[rdv_residue_strength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_residue_strength_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ bcd_leftReach ω n)
  (hwbox : w ∈ rect 0 n 0 n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ bcd_leftReach ω n) :
-- imply
  (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) := by
-- proof
  apply StatMech.Universality.rdv_residue_strength ω n hv hwbox hadj hw

/--
[rdv_face_frame_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_face_frame_dichotomy_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  (bcd_leftReach ω n).Finite ∧ (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n → (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n → (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧ (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧ (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle ∧ (fci_faceWalk_to_dualWalk (bcd_leftReach ω n) c).IsCycle) := by
-- proof
  apply StatMech.Universality.rdv_face_frame_dichotomy ω n hn hnoH

/--
[rdv_both_targets_false_on_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_both_targets_false_on_witness_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ jex_DualBarrierVCrossing bcc_wallCfg 2 ∧ ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.rdv_both_targets_false_on_witness

/--
[rdv_witness_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean)
-/
@[path]
private lemma rdv_witness_separates_eq
  {x y : Site 2}
-- given
  (hx : x ∈ leftSide 0 2 0 2)
  (hy : y ∈ rightSide 0 2 0 2) :
-- imply
  ¬ (latticeMinusBarrier (bcd_leftReach bcc_wallCfg 2)).Reachable x y := by
-- proof
  apply StatMech.Universality.rdv_witness_separates hx hy


-- created on 2026-10-23
