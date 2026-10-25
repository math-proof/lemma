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
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part3


namespace StatMech

namespace Exact3D

namespace StableBlockWithRemainder

theorem ofLinearRowSum_step {n : ℕ}
    (linear : Fin n → Fin n → ℝ) {enclosure : RatInterval.IntervalMatrix n n}
    (enclosure_sound : RatInterval.MatrixMem linear enclosure)
    (linear_contraction : RatInterval.RowSumContraction enclosure)
    (x : Fin n → ℝ) :
    (ofLinearRowSum linear enclosure_sound linear_contraction).step x =
      fun i => RatInterval.matVec linear x i := by
  funext i
  simp [ofLinearRowSum, step]


end StableBlockWithRemainder
end Exact3D
end StatMech
