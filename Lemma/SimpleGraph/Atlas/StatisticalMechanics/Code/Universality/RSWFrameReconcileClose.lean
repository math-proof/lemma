import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWFrameReconcileClose.Part3
open Set SimpleGraph MeasureTheory StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[rfr_rotbox_dichotomy_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_rotbox_dichotomy_false_eq :
-- imply
  ¬ DualVerticalCrossing bcc_wallCfg (-2) 0 0 2 := by
-- proof
  apply StatMech.Universality.rfr_rotbox_dichotomy_false

/--
[rfr_negCut_open_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_negCut_open_snd_eq_eq
  {u v : Site 2}
-- given
  (h : IsOpenEdge 2 (des_negConfig des_cutConfig) u v) :
-- imply
  u 1 = v 1 := by
-- proof
  apply StatMech.Universality.rfr_negCut_open_snd_eq h

/--
[rfr_negCut_connectedWithin_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_negCut_connectedWithin_snd_eq_eq
  {S : Set (Site 2)}
  {x y : S}
-- given
  (h : ConnectedWithin 2 (des_negConfig des_cutConfig) S x y) :
-- imply
  (x : Site 2) 1 = (y : Site 2) 1 := by
-- proof
  apply StatMech.Universality.rfr_negCut_connectedWithin_snd_eq h

/--
[rfr_inplace_closedV_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_inplace_closedV_false_eq
  {n : ℤ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ VerticalCrossing (des_negConfig des_cutConfig) 0 n 0 n := by
-- proof
  apply StatMech.Universality.rfr_inplace_closedV_false n hn

/--
[rfr_all_frames_fail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_all_frames_fail_eq :
-- imply
  (¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2) ∧ (¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg (-2) 0 0 2) ∧ (¬ HorizontalCrossing des_cutConfig 0 2 0 2 ∧ ¬ VerticalCrossing (des_negConfig des_cutConfig) 0 2 0 2) := by
-- proof
  apply StatMech.Universality.rfr_all_frames_fail

/--
[rfr_dualV_eq_negH_rotbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_dualV_eq_negH_rotbox_eq
  {n : ℤ} :
-- imply
  dualVerticalCrossingEvent 0 n 0 n = {ω | HorizontalCrossing (des_negConfig ω) 0 n (-n) 0} := by
-- proof
  apply StatMech.Universality.rfr_dualV_eq_negH_rotbox n

/--
[rfr_dualV_prob_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_dualV_prob_eq_eq
  {n : ℤ}
-- given
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n)) :
-- imply
  rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rfr_dualV_prob_eq n hmeasV

/--
[rfr_dual_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_dual_measurePreserving_eq :
-- imply
  MeasurePreserving (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) rba_selfDualMeasure rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.rfr_dual_measurePreserving

/--
[rfr_square_half_of_dominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_square_half_of_dominates_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hdom : rfr_DualCrossingDominates n)
  (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rfr_square_half_of_dominates n hmeasH hmeasV hdom hsqsym

/--
[rfr_dominates_of_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_dominates_of_pointwise_eq
  {n : ℤ}
-- given
  (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) :
-- imply
  rfr_DualCrossingDominates n := by
-- proof
  apply StatMech.Universality.rfr_dominates_of_pointwise n hsep

/--
[rfr_dominates_iff_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_dominates_iff_half_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  rfr_DualCrossingDominates n ↔ (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rfr_dominates_iff_half n hmeasH hmeasV hsqsym

/--
[rfr_symmetric_box_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_symmetric_box_false_eq
  {n : ℤ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ ((horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rfr_symmetric_box_false n hn

/--
[rfr_matched_rect_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_matched_rect_half_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 (n + 1) 0 n))
  (hmatched : rfr_MatchedPlanarDuality n)
  (hsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 (n + 1) 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
-- proof
  apply StatMech.Universality.rfr_matched_rect_half n hmeasH hmeasV hmatched hsym

/--
[rfr_square_half_of_matched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_square_half_of_matched_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 (n + 1) 0 n))
  (hmatched : rfr_MatchedPlanarDuality n)
  (hsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 (n + 1) 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rfr_square_half_of_matched n hn hmeasH hmeasV hmatched hsym

/--
[rfr_face_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_face_dualCircuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.rfr_face_dualCircuit ω n hn hnoH

/--
[rfr_no_frameReconcile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean)
-/
@[path]
private lemma rfr_no_frameReconcile_eq :
-- imply
  ¬ ∃ Φ : Site 2 → Site 2, rdv_FrameReconcile Φ := by
-- proof
  apply StatMech.Universality.rfr_no_frameReconcile


-- created on 2026-10-23
