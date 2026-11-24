module
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.Pi
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part19


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

noncomputable def affineRationalCenterExactClosedBallCertificateRelaxed :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap matrix offset x i) :=
  affineRationalCenterExactClosedBallCertificate.with_larger_radius
    (radius' := (1 : ℝ))
    (by
      norm_num [affineRationalCenterExactClosedBallCertificate,
        closedBallContractionCertificate_of_columnSumContraction_affine_and_nonnegRationalCenter,
        closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector,
        closedBallContractionCertificate_of_columnSumContraction_affine])


end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
