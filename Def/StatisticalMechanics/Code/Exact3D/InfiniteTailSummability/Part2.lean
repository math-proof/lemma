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
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]


namespace InfiniteTailCertificate

variable (C : InfiniteTailCertificate α)


def with_larger_tailBound {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    InfiniteTailCertificate α where
  finitePrefix := C.finitePrefix
  weight := C.weight
  prefixWeight := C.prefixWeight
  tailWeight := C.tailWeight
  tailBound := tailBound'
  prefix_eq_weight_on_prefix := C.prefix_eq_weight_on_prefix
  prefixWeight_zero_off_prefix := C.prefixWeight_zero_off_prefix
  tailWeight_zero_on_prefix := C.tailWeight_zero_on_prefix
  decomposition := C.decomposition
  prefixWeight_nonneg := C.prefixWeight_nonneg
  tailWeight_nonneg := C.tailWeight_nonneg
  summable_tail := C.summable_tail
  tail_tsum_le := le_trans C.tail_tsum_le hle

end InfiniteTailCertificate
end TailSummability
end Exact3D
end StatMech
