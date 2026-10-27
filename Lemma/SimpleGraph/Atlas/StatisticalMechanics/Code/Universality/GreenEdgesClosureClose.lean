import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part6
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[gec2_cut_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_cut_noH_eq
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ HorizontalCrossing des_cutConfig 0 (n + 1) 0 n := by
-- proof
  apply StatMech.Universality.gec2_cut_noH n hn

/--
[gec2_cut_no_matchedFrameDualV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_cut_no_matchedFrameDualV_eq
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ mpd_MatchedFrameDualV des_cutConfig n := by
-- proof
  apply StatMech.Universality.gec2_cut_no_matchedFrameDualV n hn

/--
[gec2_matchedFrameDualV_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_matchedFrameDualV_false_eq
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ (∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 (n + 1) 0 n → mpd_MatchedFrameDualV ω n) := by
-- proof
  apply StatMech.Universality.gec2_matchedFrameDualV_false n hn

/--
[gec2_rot90_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_rot90_rect_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rect 0 (n + 1) 0 n ↔ rot90Fun x ∈ rect (-n) 0 0 (n + 1) := by
-- proof
  apply StatMech.Universality.gec2_rot90_rect n x

/--
[gec2_rot90_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_rot90_leftSide_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ leftSide 0 (n + 1) 0 n ↔ rot90Fun x ∈ bottomSide (-n) 0 0 (n + 1) := by
-- proof
  apply StatMech.Universality.gec2_rot90_leftSide n x

/--
[gec2_rot90_rightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_rot90_rightSide_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rightSide 0 (n + 1) 0 n ↔ rot90Fun x ∈ topSide (-n) 0 0 (n + 1) := by
-- proof
  apply StatMech.Universality.gec2_rot90_rightSide n x

/--
[gec2_matchedFrameDualV_iff_closedH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_matchedFrameDualV_iff_closedH_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  mpd_MatchedFrameDualV ω n ↔ HorizontalCrossing (des_negConfig ω) 0 (n + 1) 0 n := by
-- proof
  apply StatMech.Universality.gec2_matchedFrameDualV_iff_closedH ω n

/--
[gec2_greenConfig_ge_negConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_greenConfig_ge_negConfig_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  des_negConfig ω ≤ gec2_greenConfig ω n := by
-- proof
  apply StatMech.Universality.gec2_greenConfig_ge_negConfig ω n

/--
[gec2_greenMatchedFrame_of_matchedFrameDualV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_greenMatchedFrame_of_matchedFrameDualV_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : mpd_MatchedFrameDualV ω n) :
-- imply
  gec2_GreenMatchedFrame ω n := by
-- proof
  apply StatMech.Universality.gec2_greenMatchedFrame_of_matchedFrameDualV ω n h

/--
[gec2_negConfig_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_negConfig_bot_eq
  {e : Sym2 (Site 2)} :
-- imply
  des_negConfig bcc_botCfg e = true := by
-- proof
  apply StatMech.Universality.gec2_negConfig_bot e

/--
[gec2_negBot_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_negBot_horizontalCrossing_eq
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  HorizontalCrossing (des_negConfig bcc_botCfg) 0 (n + 1) 0 n := by
-- proof
  apply StatMech.Universality.gec2_negBot_horizontalCrossing n hn

/--
[gec2_greenMatchedFrame_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_greenMatchedFrame_nonvacuous_eq
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n ∧ gec2_GreenMatchedFrame bcc_botCfg n := by
-- proof
  apply StatMech.Universality.gec2_greenMatchedFrame_nonvacuous n hn

/--
[gec2_cut_stub_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_cut_stub_bottom_eq
  {n b : ℤ}
-- given
  (h0 : 0 ≤ b)
  (hbn : b ≤ n) :
-- imply
  dualConfig des_cutConfig s(![-b, 0], ![-b, 1]) = true ∧ (![-b, 0] : Site 2) ∈ bottomSide (-n) 0 0 (n + 1) := by
-- proof
  apply StatMech.Universality.gec2_cut_stub_bottom n b h0 hbn

/--
[gec2_face_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_face_dualCircuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (mpd_leftReach ω n)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.gec2_face_dualCircuit ω hn hnoH

/--
[gec2_dichotomy_of_greenJordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_dichotomy_of_greenJordan_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (_hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n)
  (h : gec2_GreenJordan ω n) :
-- imply
  HorizontalCrossing ω 0 (n + 1) 0 n ∨ gec2_GreenMatchedFrame ω n := by
-- proof
  apply StatMech.Universality.gec2_dichotomy_of_greenJordan ω n _hnoH h

/--
[gec2_greenJordan_of_matchedFrameDualV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_greenJordan_of_matchedFrameDualV_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : mpd_MatchedFrameDualV ω n) :
-- imply
  gec2_GreenJordan ω n := by
-- proof
  apply StatMech.Universality.gec2_greenJordan_of_matchedFrameDualV ω n h

/--
[gec2_matched_half_of_greenDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_matched_half_of_greenDichotomy_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent (-n) 0 0 (n + 1)))
  (hgreen : gec2_GreenDichotomy n)
  (hsym : rba_selfDualMeasure.real (verticalCrossingEvent (-n) 0 0 (n + 1)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
-- proof
  apply StatMech.Universality.gec2_matched_half_of_greenDichotomy n hmeasH hmeasV hgreen hsym

/--
[gec2_greenDichotomy_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_greenDichotomy_iff_eq
  {n : ℤ} :
-- imply
  gec2_GreenDichotomy n ↔ ∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 (n + 1) 0 n → mpd_MatchedFrameDualV ω n := by
-- proof
  apply StatMech.Universality.gec2_greenDichotomy_iff n

/--
[gec2_greenDichotomy_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean)
-/
@[path]
private lemma gec2_greenDichotomy_false_eq
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ gec2_GreenDichotomy n := by
-- proof
  apply StatMech.Universality.gec2_greenDichotomy_false n hn


-- created on 2026-10-23
