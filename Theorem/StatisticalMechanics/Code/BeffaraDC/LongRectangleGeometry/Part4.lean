/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleSqrtTrick
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part4
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


theorem bdcLongRectangleUnion_isIncreasing (alpha n : ℕ) :
    IsIncreasing (bdcLongRectangleUnion alpha n) := by
  unfold bdcLongRectangleUnion
  exact isUpperSet_iUnion₂ (fun k _ =>
    bdcLongRectangleEvent_isIncreasing alpha n k)


theorem bdcLongRectangleUnion_measurableSet (alpha n : ℕ) :
    MeasurableSet (bdcLongRectangleUnion alpha n) := by
  unfold bdcLongRectangleUnion
  exact Finset.measurableSet_biUnion (bdcLongRectangleIndices alpha)
    (fun k _ => bdcLongRectangleEvent_measurableSet alpha n k)


end BeffaraDC
end StatMech
