/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*}


variable [DecidableEq α]


namespace FiniteSupportCertificate

variable (C : FiniteSupportCertificate α)


def with_tailEnvelope_and_tailBound (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    FiniteSupportCertificate α where
  support := C.support
  finitePrefix := C.finitePrefix
  finitePrefix_subset_support := C.finitePrefix_subset_support
  weight := C.weight
  envelope := envelope'
  tailBound := tailBound'
  zero_off_support := C.zero_off_support
  weight_nonneg := C.weight_nonneg
  envelope_nonneg_on_tail := henvelope_nonneg
  weight_le_envelope_on_tail := hweight_le
  envelope_tail_sum_le := henvelope_sum

end FiniteSupportCertificate
end TailSummability
end Exact3D
end StatMech
