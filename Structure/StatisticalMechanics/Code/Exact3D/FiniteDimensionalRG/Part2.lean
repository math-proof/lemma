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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part2


namespace StatMech

namespace Exact3D

structure StableBlockWithRemainder (n : ℕ) where
  linear : Fin n → Fin n → ℝ
  enclosure : RatInterval.IntervalMatrix n n
  enclosure_sound : RatInterval.MatrixMem linear enclosure
  linear_contraction : RatInterval.RowSumContraction enclosure
  remainder : (Fin n → ℝ) → Fin n → ℝ
  remainder_lipschitz : IntervalLipschitzConstant
  remainder_bound :
    ∀ x i, |remainder x i| ≤
      (remainder_lipschitz.upper : ℝ) * RatInterval.supNormVec x
  total_lt_one : linear_contraction.c + remainder_lipschitz.upper < 1

end Exact3D
end StatMech
