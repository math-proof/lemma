import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part5
open Set SimpleGraph Finset StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[mpd_rot90Inv_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_rot90Inv_rect_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rect a b c d ↔ rot90Inv x ∈ rect c d (-b) (-a) := by
-- proof
  apply StatMech.Universality.mpd_rot90Inv_rect a b c d x

/--
[mpd_rot90Inv_bottomSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_rot90Inv_bottomSide_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ bottomSide a b c d ↔ rot90Inv x ∈ leftSide c d (-b) (-a) := by
-- proof
  apply StatMech.Universality.mpd_rot90Inv_bottomSide a b c d x

/--
[mpd_rot90Inv_topSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_rot90Inv_topSide_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ topSide a b c d ↔ rot90Inv x ∈ rightSide c d (-b) (-a) := by
-- proof
  apply StatMech.Universality.mpd_rot90Inv_topSide a b c d x

/--
[mpd_dualV_iff_negH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_dualV_iff_negH_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ} :
-- imply
  DualVerticalCrossing ω a b c d ↔ HorizontalCrossing (des_negConfig ω) c d (-b) (-a) := by
-- proof
  apply StatMech.Universality.mpd_dualV_iff_negH ω a b c d

/--
[mpd_dualCut_snd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_dualCut_snd_le_eq
  {p q : Site 2}
-- given
  (h : IsOpenEdge 2 (dualConfig des_cutConfig) p q) :
-- imply
  p 1 ≤ 1 ∧ q 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.mpd_dualCut_snd_le h

/--
[mpd_dualCut_walk_snd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_dualCut_walk_snd_le_eq
  {S : Set (Site 2)}
  {x y : S}
-- given
  (h : ConnectedWithin 2 (dualConfig des_cutConfig) S x y)
  (hx : (x : Site 2) 1 ≤ 1) :
-- imply
  (y : Site 2) 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.mpd_dualCut_walk_snd_le h hx

/--
[mpd_no_dualV_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_no_dualV_box_eq
-- given
  (a b h : ℤ)
  (hh : 2 ≤ h) :
-- imply
  ¬ DualVerticalCrossing des_cutConfig a b 0 h := by
-- proof
  apply StatMech.Universality.mpd_no_dualV_box a b h hh

/--
[mpd_no_H_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_no_H_box_eq
-- given
  (w h : ℤ)
  (hw : 1 ≤ w) :
-- imply
  ¬ HorizontalCrossing des_cutConfig 0 w 0 h := by
-- proof
  apply StatMech.Universality.mpd_no_H_box w h hw

/--
[mpd_matched_planarDuality_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_matched_planarDuality_false_eq
  {n : ℤ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ rfr_MatchedPlanarDuality n := by
-- proof
  apply StatMech.Universality.mpd_matched_planarDuality_false n hn

/--
[mpd_corrected_box_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_corrected_box_false_eq
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ DualVerticalCrossing des_cutConfig (-n) 0 0 (n + 1) := by
-- proof
  apply StatMech.Universality.mpd_corrected_box_false n hn

/--
[mpd_leftReach_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_leftReach_subset_box_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  mpd_leftReach ω n ⊆ rect 0 (n + 1) 0 n := by
-- proof
  apply StatMech.Universality.mpd_leftReach_subset_box ω n

/--
[mpd_leftReach_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_leftReach_finite_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  (mpd_leftReach ω n).Finite := by
-- proof
  apply StatMech.Universality.mpd_leftReach_finite ω n

/--
[mpd_horizontal_iff_right_in_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_horizontal_iff_right_in_leftReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  HorizontalCrossing ω 0 (n + 1) 0 n ↔ ∃ y : Site 2, y ∈ rightSide 0 (n + 1) 0 n ∧ y ∈ mpd_leftReach ω n := by
-- proof
  apply StatMech.Universality.mpd_horizontal_iff_right_in_leftReach ω n

/--
[mpd_leftSide_subset_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_leftSide_subset_leftReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x : Site 2}
-- given
  (hx : x ∈ leftSide 0 (n + 1) 0 n) :
-- imply
  x ∈ mpd_leftReach ω n := by
-- proof
  apply StatMech.Universality.mpd_leftSide_subset_leftReach ω n hx

/--
[mpd_rightSide_notin_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_rightSide_notin_leftReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {y : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n)
  (hy : y ∈ rightSide 0 (n + 1) 0 n) :
-- imply
  y ∉ mpd_leftReach ω n := by
-- proof
  apply StatMech.Universality.mpd_rightSide_notin_leftReach ω n hnoH hy

/--
[mpd_leftReach_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_leftReach_separates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n)
  (hx : x ∈ leftSide 0 (n + 1) 0 n)
  (hy : y ∈ rightSide 0 (n + 1) 0 n) :
-- imply
  ¬ (latticeMinusBarrier (mpd_leftReach ω n)).Reachable x y := by
-- proof
  apply StatMech.Universality.mpd_leftReach_separates ω n hnoH hx hy

/--
[mpd_escape_crossCount_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_escape_crossCount_odd_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n)
  (hx : x ∈ leftSide 0 (n + 1) 0 n)
  (hy : y ∈ rightSide 0 (n + 1) 0 n) :
-- imply
  ¬ Even (crossCount (mpd_leftReach ω n) w) := by
-- proof
  apply StatMech.Universality.mpd_escape_crossCount_odd ω n hnoH hx hy w

/--
[mpd_leftReach_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_leftReach_extend_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ mpd_leftReach ω n)
  (hwbox : w ∈ rect 0 (n + 1) 0 n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hopen : ω s(v, w) = true) :
-- imply
  w ∈ mpd_leftReach ω n := by
-- proof
  apply StatMech.Universality.mpd_leftReach_extend ω n hv hwbox hadj hopen

/--
[mpd_leftReach_boundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_leftReach_boundary_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj p q)
  (hbd : bdEdge (mpd_leftReach ω n) s(p, q))
  (hpbox : p ∈ rect 0 (n + 1) 0 n)
  (hqbox : q ∈ rect 0 (n + 1) 0 n) :
-- imply
  ω s(p, q) = false := by
-- proof
  apply StatMech.Universality.mpd_leftReach_boundary_closed ω n hadj hbd hpbox hqbox

/--
[mpd_leftReach_barrier_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_leftReach_barrier_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj p q)
  (hbd : bdEdge (mpd_leftReach ω n) s(p, q))
  (hpbox : p ∈ rect 0 (n + 1) 0 n)
  (hqbox : q ∈ rect 0 (n + 1) 0 n) :
-- imply
  dualConfig ω (crossEdge s(p, q)) = true := by
-- proof
  apply StatMech.Universality.mpd_leftReach_barrier_dual_open ω n hadj hbd hpbox hqbox

/--
[mpd_edgeBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_edgeBoundary_nonempty_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) :
-- imply
  (edgeBoundary 2 (mpd_leftReach ω n)).Nonempty := by
-- proof
  apply StatMech.Universality.mpd_edgeBoundary_nonempty ω hn hnoH

/--
[mpd_exists_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_exists_dualCircuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (mpd_leftReach ω n)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.mpd_exists_dualCircuit ω hn hnoH

/--
[mpd_dichotomy_of_matchedFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_dichotomy_of_matchedFrame_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (_hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n)
  (h : mpd_MatchedFrameDualV ω n) :
-- imply
  HorizontalCrossing ω 0 (n + 1) 0 n ∨ DualVerticalCrossing ω (-n) 0 0 (n + 1) := by
-- proof
  apply StatMech.Universality.mpd_dichotomy_of_matchedFrame ω n _hnoH h

/--
[mpd_botCfg_dual_allOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_botCfg_dual_allOpen_eq
  {e : Sym2 (Site 2)} :
-- imply
  dualConfig bcc_botCfg e = true := by
-- proof
  apply StatMech.Universality.mpd_botCfg_dual_allOpen e

/--
[mpd_botCfg_dualV_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_botCfg_dualV_col_eq
  {a b c d x0 : ℤ}
-- given
  (hx : a ≤ x0 ∧ x0 ≤ b)
  (hcd : c ≤ d) :
-- imply
  DualVerticalCrossing bcc_botCfg a b c d := by
-- proof
  apply StatMech.Universality.mpd_botCfg_dualV_col a b c d x0 hx hcd

/--
[mpd_botCfg_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_botCfg_noH_eq
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n := by
-- proof
  apply StatMech.Universality.mpd_botCfg_noH n hn

/--
[mpd_matchedFrame_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_matchedFrame_nonvacuous_eq
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n ∧ mpd_MatchedFrameDualV bcc_botCfg n := by
-- proof
  apply StatMech.Universality.mpd_matchedFrame_nonvacuous n hn

/--
[mpd_literal_vs_honest_boxes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_literal_vs_honest_boxes_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  (DualVerticalCrossing ω 0 (n + 1) 0 n ↔ HorizontalCrossing (des_negConfig ω) 0 n (-(n + 1)) 0) ∧ (mpd_MatchedFrameDualV ω n ↔ HorizontalCrossing (des_negConfig ω) 0 (n + 1) 0 n) := by
-- proof
  apply StatMech.Universality.mpd_literal_vs_honest_boxes ω n

/--
[mpd_both_plain_targets_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean)
-/
@[path]
private lemma mpd_both_plain_targets_false_eq
  {n : ℤ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ HorizontalCrossing des_cutConfig 0 (n + 1) 0 n ∧ ¬ DualVerticalCrossing des_cutConfig 0 (n + 1) 0 n ∧ ¬ DualVerticalCrossing des_cutConfig (-n) 0 0 (n + 1) := by
-- proof
  apply StatMech.Universality.mpd_both_plain_targets_false n hn


-- created on 2026-10-23
