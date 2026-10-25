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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part14


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

theorem zeroMap_mapsClosedBall {n : ℕ} {radius : ℝ} (hradius : 0 ≤ radius) :
    MapsClosedBall (@zeroMap n) 0 radius :=
  (zeroMap_closedBallContractionCertificate (n := n) hradius).mapsClosedBall


theorem zeroMap_fixedPoint_eq_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : zeroMap x = x) : x = 0 := by
  have hunique := fixedPoint_unique_of_l1_contraction (@zeroMap n)
    (by norm_num : (0 : ℝ) < 1) zeroMap_lipschitz_zero hx rfl
  simpa [zeroMap] using hunique

end FiniteContraction
end Exact3D
end StatMech
