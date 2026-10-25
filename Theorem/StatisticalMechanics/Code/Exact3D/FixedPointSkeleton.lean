/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.Pi
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

theorem l1Dist_nonneg {n : ℕ} (x y : Fin n → ℝ) :
    0 ≤ l1Dist x y :=
  RatInterval.supNormVec_nonneg _


theorem abs_sub_coord_le_l1Dist {n : ℕ} (x y : Fin n → ℝ) (i : Fin n) :
    |x i - y i| ≤ l1Dist x y :=
  RatInterval.abs_coord_le_supNormVec (fun i => x i - y i) i


theorem eq_of_l1Dist_eq_zero {n : ℕ} {x y : Fin n → ℝ}
    (h : l1Dist x y = 0) : x = y := by
  funext i
  have habs_nonpos : |x i - y i| ≤ 0 := by
    simpa [h] using abs_sub_coord_le_l1Dist x y i
  have habs_zero : |x i - y i| = 0 :=
    le_antisymm habs_nonpos (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs_zero)


end FiniteContraction
end Exact3D
end StatMech
