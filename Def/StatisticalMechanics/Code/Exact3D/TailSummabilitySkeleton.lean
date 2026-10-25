/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Structure.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*}


variable [DecidableEq α]


namespace FiniteSupportCertificate

variable (C : FiniteSupportCertificate α)


def tailSupport : Finset α :=
  C.support \ C.finitePrefix

end FiniteSupportCertificate
end TailSummability
end Exact3D
end StatMech
