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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part18


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

noncomputable def affineRationalCenterExactClosedBallCertificate :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap matrix offset x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine_and_nonnegRationalCenter
    columnSumContraction matrix_mem_intervals intervals_nonnegative
    offset_mem_intervals centerQ centerQ_nonnegative
    (radius := 0) (by norm_num) affineResidualNonneg_absSum_le_radius_zero


end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
