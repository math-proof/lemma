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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part2


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

noncomputable def iterate {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) :
    ℕ → (Fin n → ℝ) → Fin n → ℝ
  | 0, x => x
  | k + 1, x => F (iterate F k x)


end FiniteContraction
end Exact3D
end StatMech
