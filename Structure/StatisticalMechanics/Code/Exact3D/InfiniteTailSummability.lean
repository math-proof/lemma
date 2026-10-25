/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]


structure InfiniteTailCertificate (α : Type*) [DecidableEq α] where
  finitePrefix : Finset α
  weight : α → ℝ
  prefixWeight : α → ℝ
  tailWeight : α → ℝ
  tailBound : ℝ
  prefix_eq_weight_on_prefix :
    ∀ a, a ∈ finitePrefix → prefixWeight a = weight a
  prefixWeight_zero_off_prefix :
    ∀ a, a ∉ finitePrefix → prefixWeight a = 0
  tailWeight_zero_on_prefix :
    ∀ a, a ∈ finitePrefix → tailWeight a = 0
  decomposition :
    ∀ a, weight a = prefixWeight a + tailWeight a
  prefixWeight_nonneg : ∀ a, 0 ≤ prefixWeight a
  tailWeight_nonneg : ∀ a, 0 ≤ tailWeight a
  summable_tail : Summable tailWeight
  tail_tsum_le : (∑' a, tailWeight a) ≤ tailBound

end TailSummability
end Exact3D
end StatMech
