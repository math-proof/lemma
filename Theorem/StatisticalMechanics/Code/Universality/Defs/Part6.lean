/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.Universality.Defs.Part5
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


@[simp]
theorem translatedHorizontalCrossingEvent_zero (a b : ℤ) :
    translatedHorizontalCrossingEvent (0 : Site 2) a b = horizontalCrossingEvent a b := by
  unfold translatedHorizontalCrossingEvent
  have : (translateConfig (0 : Site 2)) = id := funext translateConfig_zero
  rw [this, Set.preimage_id]


@[simp]
theorem translatedVerticalCrossingEvent_zero (a b : ℤ) :
    translatedVerticalCrossingEvent (0 : Site 2) a b = verticalCrossingEvent a b := by
  unfold translatedVerticalCrossingEvent
  have : (translateConfig (0 : Site 2)) = id := funext translateConfig_zero
  rw [this, Set.preimage_id]


end Universality
end StatMech
