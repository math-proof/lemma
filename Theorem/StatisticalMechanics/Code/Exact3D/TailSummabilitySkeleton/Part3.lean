/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Def.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*}


variable [DecidableEq α]


namespace FiniteSupportCertificate

variable (C : FiniteSupportCertificate α)


@[simp] theorem with_larger_tailBound_support {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).support = C.support :=
  rfl

@[simp] theorem with_larger_tailBound_finitePrefix {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).finitePrefix = C.finitePrefix :=
  rfl

@[simp] theorem with_larger_tailBound_weight {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).weight = C.weight :=
  rfl

@[simp] theorem with_larger_tailBound_envelope {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).envelope = C.envelope :=
  rfl

@[simp] theorem with_larger_tailBound_tailBound {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).tailBound = tailBound' :=
  rfl


end FiniteSupportCertificate
end TailSummability
end Exact3D
end StatMech
