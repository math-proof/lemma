/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentLimitTranslation.Part2
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


noncomputable def currentShiftLaw {E H : Type*} [Countable E]
    [Group H] [MulAction H E] (g : H)
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    ProbabilityMeasure (InfiniteCurrentConfig E) :=
  mu.map (continuous_currentShift g).measurable.aemeasurable

end StatMech.FrontierB
