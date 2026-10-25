/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificate


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem abs_coord_le_supNormVec {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ supNormVec x := by
  classical
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (by simp)

theorem supNormVec_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ supNormVec x := by
  classical
  exact Finset.sum_nonneg fun i _ => abs_nonneg (x i)


end RatInterval
end Exact3D
end StatMech
