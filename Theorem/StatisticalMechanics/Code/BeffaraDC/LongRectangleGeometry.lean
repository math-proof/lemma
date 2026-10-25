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
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


theorem bdcLongRectangleXOffset_lt_period {alpha n : ℕ} (hn : 0 < n)
    (k : BdcLongRectangleIndex alpha) :
    bdcLongRectangleXOffset n k < bdcLongRectanglePeriod alpha n := by
  unfold bdcLongRectangleXOffset bdcLongRectanglePeriod
  exact Nat.mul_lt_mul_of_pos_right k.1.isLt hn


theorem bdcLongRectangleYOffset_lt_period {alpha n : ℕ} (ha : 0 < alpha)
    (hn : 0 < n) (k : BdcLongRectangleIndex alpha) :
    bdcLongRectangleYOffset n k < bdcLongRectanglePeriod alpha n := by
  unfold bdcLongRectangleYOffset bdcLongRectanglePeriod
  have hm : 0 < 2 * alpha * n := by positivity
  have h := Nat.mul_lt_mul_of_pos_right k.2.isLt hm
  nlinarith


end BeffaraDC
end StatMech
