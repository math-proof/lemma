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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part16


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

theorem center_fixedPoint :
    (fun x i => RatInterval.affineMap matrix offset x i)
      (fun _ : Fin 1 => (1 / 2 : ℝ)) =
      (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
  funext i
  fin_cases i
  norm_num [RatInterval.affineMap, RatInterval.matVec, matrix, matrixQ,
    offset, offsetQ]


end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
