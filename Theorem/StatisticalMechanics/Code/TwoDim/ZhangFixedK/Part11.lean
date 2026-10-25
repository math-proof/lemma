/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part11
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_FaithfulDualVerticalEvent_measurableSet (N : ℕ) :
    MeasurableSet (zfk_FaithfulDualVerticalEvent N) := by
  exact (rlc_verticalCrossingEvent_measurableSet _ _ _ _).preimage
    fci_faceDualConfig_measurePreserving.measurable


theorem zfk_faithfulDualVertical_prob_eq_matched (N : ℕ) :
    halfMeasure.real (zfk_FaithfulDualVerticalEvent N) =
      halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) := by
  have hmeasSwap : MeasurableSet
      (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ) - 1) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :=
    rlc_horizontalCrossingEvent_measurableSet _ _ _ _
  calc
    halfMeasure.real (zfk_FaithfulDualVerticalEvent N) =
        halfMeasure.real (zfk_FaceVerticalEvent N) := by
      exact fci_faceDualConfig_measurePreserving.measureReal_preimage
        (rlc_verticalCrossingEvent_measurableSet _ _ _ _).nullMeasurableSet
    _ = halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ) - 1) (N : ℤ) (-(N : ℤ)) (N : ℤ)) := by
      exact crf_verticalCrossing_eq_horizontal_swap
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ) - 1) (N : ℤ) hmeasSwap
    _ = halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) := by
      symm
      simpa using cti_horizontalCrossing_translation_invariant
        (-(N : ℤ) - 1) (N : ℤ) (-(N : ℤ)) (N : ℤ)
        (![1, 0] : Site 2) hmeasSwap


end StatMech.TwoDim
