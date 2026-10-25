/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part5


namespace StatMech

namespace Exact3D

namespace RatInterval

structure RowSumContraction {n : ℕ} (I : IntervalMatrix n n) where
  c : ℚ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  row_bound : ∀ i, MatrixAbsRowSum I i ≤ c


structure ColumnSumContraction {n : ℕ} (I : IntervalMatrix n n) where
  c : ℚ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  col_bound : ∀ j, MatrixAbsColSum I j ≤ c


end RatInterval
end Exact3D
end StatMech
