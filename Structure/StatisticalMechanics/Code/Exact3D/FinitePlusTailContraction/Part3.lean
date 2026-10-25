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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part10
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

structure FinitePlusTailLipschitzCertificate (n : ℕ) (α : Type*) where
  map : FinitePlusTailState n α → FinitePlusTailState n α
  finiteToFinite : ℝ
  tailToFinite : ℝ
  finiteToTail : ℝ
  tailToTail : ℝ
  c : ℝ
  finiteToFinite_nonneg : 0 ≤ finiteToFinite
  tailToFinite_nonneg : 0 ≤ tailToFinite
  finiteToTail_nonneg : 0 ≤ finiteToTail
  tailToTail_nonneg : 0 ≤ tailToTail
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  finite_bound :
    ∀ x y,
      (map x).finiteDist (map y) ≤
        finiteToFinite * x.finiteDist y + tailToFinite * x.tailDist y
  tail_bound :
    ∀ x y,
      (map x).tailDist (map y) ≤
        finiteToTail * x.finiteDist y + tailToTail * x.tailDist y
  finite_column_sum_le : finiteToFinite + finiteToTail ≤ c
  tail_column_sum_le : tailToFinite + tailToTail ≤ c

end Exact3D
end StatMech
