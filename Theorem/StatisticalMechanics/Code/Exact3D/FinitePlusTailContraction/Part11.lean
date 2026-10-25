/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Structure.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part3
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailLipschitzCertificate

variable {n : ℕ} {α : Type*}


theorem mixed_lipschitz
    (C : FinitePlusTailLipschitzCertificate n α) :
    ∀ x y, (C.map x).dist (C.map y) ≤ C.c * x.dist y := by
  intro x y
  have hfinite_nonneg : 0 ≤ x.finiteDist y :=
    FinitePlusTailState.finiteDist_nonneg x y
  have htail_nonneg : 0 ≤ x.tailDist y :=
    FinitePlusTailState.tailDist_nonneg x y
  calc
    (C.map x).dist (C.map y) =
        (C.map x).finiteDist (C.map y) +
          (C.map x).tailDist (C.map y) := rfl
    _ ≤
        (C.finiteToFinite * x.finiteDist y +
          C.tailToFinite * x.tailDist y) +
        (C.finiteToTail * x.finiteDist y +
          C.tailToTail * x.tailDist y) := by
      exact add_le_add (C.finite_bound x y) (C.tail_bound x y)
    _ =
        (C.finiteToFinite + C.finiteToTail) * x.finiteDist y +
          (C.tailToFinite + C.tailToTail) * x.tailDist y := by
      ring
    _ ≤ C.c * x.finiteDist y + C.c * x.tailDist y := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right C.finite_column_sum_le hfinite_nonneg)
        (mul_le_mul_of_nonneg_right C.tail_column_sum_le htail_nonneg)
    _ = C.c * x.dist y := by
      simp [FinitePlusTailState.dist, FinitePlusTailState.finiteDist,
        FinitePlusTailState.tailDist]
      ring_nf


end FinitePlusTailLipschitzCertificate
end Exact3D
end StatMech
