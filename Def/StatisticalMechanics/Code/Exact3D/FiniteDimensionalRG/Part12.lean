/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part10


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplittingExample

def stableRowSumContraction :
    RatInterval.RowSumContraction stableEnclosure where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  row_bound := by
    intro i
    fin_cases i
    norm_num [RatInterval.MatrixAbsRowSum, stableEnclosure,
      RatInterval.point, RatInterval.absUpper]


def zeroRemainderLipschitz : IntervalLipschitzConstant where
  interval := RatInterval.point 0
  nonnegative := by norm_num [RatInterval.point, RatInterval.Nonnegative]


noncomputable def stableBlock : StableBlockWithRemainder 1 where
  linear := stableLinear
  enclosure := stableEnclosure
  enclosure_sound := stableLinear_mem_enclosure
  linear_contraction := stableRowSumContraction
  remainder := fun _ _ => 0
  remainder_lipschitz := zeroRemainderLipschitz
  remainder_bound := by
    intro x i
    simp [zeroRemainderLipschitz, IntervalLipschitzConstant.upper,
      RatInterval.point]
  total_lt_one := by
    norm_num [stableRowSumContraction, zeroRemainderLipschitz,
      IntervalLipschitzConstant.upper, RatInterval.point]


end FiniteHyperbolicSplittingExample
end Exact3D
end StatMech
