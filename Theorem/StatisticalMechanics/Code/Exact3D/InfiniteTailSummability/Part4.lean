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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]


namespace FiniteSupportCertificate

variable (C : FiniteSupportCertificate α)


@[simp] theorem toInfiniteTailCertificate_finitePrefix :
    C.toInfiniteTailCertificate.finitePrefix = C.finitePrefix :=
  rfl

@[simp] theorem toInfiniteTailCertificate_weight :
    C.toInfiniteTailCertificate.weight = C.weight :=
  rfl

@[simp] theorem toInfiniteTailCertificate_tailBound :
    C.toInfiniteTailCertificate.tailBound = C.tailBound :=
  rfl


theorem toInfiniteTailCertificate_tsum_weight_le_prefix_add_tailBound :
    (∑' a, C.toInfiniteTailCertificate.weight a) ≤
      C.toInfiniteTailCertificate.prefixSum + C.tailBound := by
  simpa using
    C.toInfiniteTailCertificate.tsum_weight_le_prefixSum_add_tailBound

end FiniteSupportCertificate
end TailSummability
end Exact3D
end StatMech
