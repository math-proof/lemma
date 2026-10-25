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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]


namespace InfiniteTailCertificate

variable (C : InfiniteTailCertificate α)


@[simp] theorem with_larger_tailBound_finitePrefix {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).finitePrefix = C.finitePrefix :=
  rfl

@[simp] theorem with_larger_tailBound_weight {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).weight = C.weight :=
  rfl

@[simp] theorem with_larger_tailBound_prefixWeight {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).prefixWeight = C.prefixWeight :=
  rfl

@[simp] theorem with_larger_tailBound_tailWeight {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).tailWeight = C.tailWeight :=
  rfl

@[simp] theorem with_larger_tailBound_tailBound {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).tailBound = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_prefixSum {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).prefixSum = C.prefixSum :=
  rfl


end InfiniteTailCertificate
end TailSummability
end Exact3D
end StatMech
