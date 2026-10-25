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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part12


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

theorem residual_l1Dist_le_of_vectorMem {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {center : Fin n → ℝ}
    {R : RatInterval.IntervalVector n}
    (hR : RatInterval.VectorMem (fun i => F center i - center i) R) :
    l1Dist (F center) center ≤ (RatInterval.VectorAbsSum R : ℝ) := by
  unfold l1Dist RatInterval.supNormVec
  exact RatInterval.VectorMem.abs_sum_le hR


end FiniteContraction
end Exact3D
end StatMech
