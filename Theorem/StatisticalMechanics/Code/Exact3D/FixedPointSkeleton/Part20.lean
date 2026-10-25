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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part20


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

theorem exists_fixedPoint_in_relaxed_exact_ball :
    ∃ p : Fin 1 → ℝ,
      (fun x i => RatInterval.affineMap matrix offset x i) p = p ∧
      ClosedBall (fun _ : Fin 1 => (1 / 2 : ℝ)) 1 p :=
  by
    simpa [affineRationalCenterExactClosedBallCertificateRelaxed,
      affineRationalCenterExactClosedBallCertificate,
      ClosedBallContractionCertificate.with_larger_radius,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_nonnegRationalCenter,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector,
      closedBallContractionCertificate_of_columnSumContraction_affine, centerQ]
      using affineRationalCenterExactClosedBallCertificateRelaxed.exists_fixedPoint


theorem selectedFixedPoint_eq_center :
    affineRationalCenterClosedBallCertificate.fixedPoint =
      (fun _ : Fin 1 => (1 / 2 : ℝ)) :=
  affineRationalCenterClosedBallCertificate.fixedPoint_unique
    affineRationalCenterClosedBallCertificate.fixedPoint_isFixed center_fixedPoint


theorem selectedExactFixedPoint_eq_center :
    affineRationalCenterExactClosedBallCertificate.fixedPoint =
      (fun _ : Fin 1 => (1 / 2 : ℝ)) :=
  affineRationalCenterExactClosedBallCertificate.fixedPoint_unique
    affineRationalCenterExactClosedBallCertificate.fixedPoint_isFixed
    center_fixedPoint

end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
