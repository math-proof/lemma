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
import Structure.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]


namespace InfiniteTailCertificate

variable (C : InfiniteTailCertificate α)


def prefixSum : ℝ :=
  ∑ a ∈ C.finitePrefix, C.weight a


end InfiniteTailCertificate
end TailSummability
end Exact3D
end StatMech
