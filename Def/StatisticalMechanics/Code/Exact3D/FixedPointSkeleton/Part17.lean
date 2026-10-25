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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part16


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

noncomputable def exactClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap matrix offset x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine
    columnSumContraction matrix_mem_intervals offset
    (fun _ : Fin 1 => (1 / 2 : ℝ)) hradius (by
      have hnonneg :
          0 ≤ (1 - (columnSumContraction.c : ℝ)) * radius := by
        exact mul_nonneg (by norm_num [columnSumContraction]) hradius
      rw [center_fixedPoint]
      simpa [l1Dist_self] using hnonneg)


end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
