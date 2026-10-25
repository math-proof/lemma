/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part12
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_faceDualRect_half_law (n : ℤ)
    (hmeas : MeasurableSet (crr_FaceRectVerticalEvent n)) :
    rba_selfDualMeasure.real (crr_FaceDualRectEvent n) =
      rba_selfDualMeasure.real (crr_FaceRectVerticalEvent n) := by
  exact fci_faceDualConfig_measurePreserving.measureReal_preimage hmeas.nullMeasurableSet


theorem crr_faceRectVertical_real_le_square (n : ℤ) (hn : 0 < n)
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    rba_selfDualMeasure.real (crr_FaceRectVerticalEvent n) ≤
      rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  calc
    rba_selfDualMeasure.real (crr_FaceRectVerticalEvent n) =
        rba_selfDualMeasure.real (horizontalCrossingEvent (-1) n 0 (n - 1)) := by
      exact crf_verticalCrossing_eq_horizontal_swap 0 (n - 1) (-1) n hmeasThin
    _ = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 (n - 1)) := by
      symm
      simpa using cti_horizontalCrossing_translation_invariant (-1) n 0 (n - 1)
        (![1, 0] : Site 2) hmeasThin
    _ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) :=
      measureReal_mono (crr_horizontalCrossing_faceBand_subset n hn)
    _ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) :=
      bxa_horizontalCrossing_real_mono_width hn (by omega)


theorem crr_square_compl_subset_faceDualRect (n : ℤ) (hn : 0 ≤ n)
    (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ crr_FaceDualRectEvent n := by
  intro ω hnoH
  apply crr_verticalCrossing_of_barrierConnectsRows ω n hnoH
  exact crr_barrierConnectsRows_of_leftFillInteriorArc ω n hn hnoH
    (crr_leftFillInteriorArc_of_frameArcOrder ω n (horder ω))


theorem crr_square_compl_subset_faceDualRect_unconditional (n : ℤ) (hn : 0 ≤ n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ crr_FaceDualRectEvent n := by
  intro ω hnoH
  exact crr_verticalCrossing_of_barrierConnectsRows ω n hnoH
    (crr_barrierConnectsRows ω n hn hnoH)


theorem crr_square_half_of_frameArcOrder (n : ℤ) (hn : 0 < n)
    (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ ≤
      rba_selfDualMeasure.real (crr_FaceDualRectEvent n) :=
    measureReal_mono (crr_square_compl_subset_faceDualRect n (le_of_lt hn) horder)
  rw [measureReal_compl hmeasH, probReal_univ,
    crr_faceDualRect_half_law n hmeasFace] at hmono
  have hcomp := crr_faceRectVertical_real_le_square n hn hmeasThin
  linarith


theorem crr_square_half (n : ℤ) (hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ ≤
      rba_selfDualMeasure.real (crr_FaceDualRectEvent n) :=
    measureReal_mono (crr_square_compl_subset_faceDualRect_unconditional n (le_of_lt hn))
  rw [measureReal_compl hmeasH, probReal_univ,
    crr_faceDualRect_half_law n hmeasFace] at hmono
  have hcomp := crr_faceRectVertical_real_le_square n hn hmeasThin
  linarith


end Universality
end StatMech
