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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace ZeroLinearExample

theorem mapsClosedBall {radius : ℝ} (hradius : 0 ≤ radius) :
    MapsClosedBall (fun x i => RatInterval.matVec matrix x i) (0 : Fin 1 → ℝ)
      radius :=
  (closedBallCertificate hradius).mapsClosedBall


theorem mapsClosedBall_from_rationalCenter {radius : ℝ} (hradius : 0 ≤ radius) :
    MapsClosedBall (fun x i => RatInterval.matVec matrix x i)
      (fun _ : Fin 1 => (0 : ℝ)) radius :=
  by
    simpa [rationalCenterClosedBallCertificate,
      closedBallContractionCertificate_of_columnSumContraction_and_rationalCenter,
      closedBallContractionCertificate_of_columnSumContraction_and_residualVector,
      closedBallContractionCertificate_of_columnSumContraction, centerQ] using
      (rationalCenterClosedBallCertificate hradius).mapsClosedBall


theorem mapsClosedBall_from_affineRationalCenter {radius : ℝ}
    (hradius : 0 ≤ radius) :
    MapsClosedBall (fun x i => RatInterval.affineMap matrix offset x i)
      (fun _ : Fin 1 => (0 : ℝ)) radius :=
  by
    simpa [affineRationalCenterClosedBallCertificate,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_rationalCenter,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector,
      closedBallContractionCertificate_of_columnSumContraction_affine, centerQ,
      offset] using
      (affineRationalCenterClosedBallCertificate hradius).mapsClosedBall

end ZeroLinearExample
end FiniteContraction
end Exact3D
end StatMech
