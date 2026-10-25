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
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]


namespace FiniteSupportCertificate

variable (C : FiniteSupportCertificate α)


noncomputable def toInfiniteTailCertificate :
    InfiniteTailCertificate α where
  finitePrefix := C.finitePrefix
  weight := C.weight
  prefixWeight := fun a => if a ∈ C.finitePrefix then C.weight a else 0
  tailWeight := fun a => if a ∈ C.finitePrefix then 0 else C.weight a
  tailBound := C.tailBound
  prefix_eq_weight_on_prefix := by
    intro a ha
    simp [ha]
  prefixWeight_zero_off_prefix := by
    intro a ha
    simp [ha]
  tailWeight_zero_on_prefix := by
    intro a ha
    simp [ha]
  decomposition := by
    intro a
    by_cases ha : a ∈ C.finitePrefix <;> simp [ha]
  prefixWeight_nonneg := by
    intro a
    by_cases ha : a ∈ C.finitePrefix
    · simpa [ha] using C.weight_nonneg a
    · simp [ha]
  tailWeight_nonneg := by
    intro a
    by_cases ha : a ∈ C.finitePrefix
    · simp [ha]
    · simpa [ha] using C.weight_nonneg a
  summable_tail := by
    refine summable_of_ne_finset_zero (s := C.support) ?_
    intro a ha
    by_cases hprefix : a ∈ C.finitePrefix
    · simp [hprefix]
    · simp [hprefix, C.zero_off_support a ha]
  tail_tsum_le := by
    let tailWeight : α → ℝ :=
      fun a => if a ∈ C.finitePrefix then 0 else C.weight a
    have hzero :
        ∀ a, a ∉ C.tailSupport → tailWeight a = 0 := by
      intro a ha
      by_cases hprefix : a ∈ C.finitePrefix
      · simp [tailWeight, hprefix]
      · have hnotSupport : a ∉ C.support := by
          intro hsupport
          exact ha (by simp [FiniteSupportCertificate.tailSupport,
            hsupport, hprefix])
        simp [tailWeight, hprefix, C.zero_off_support a hnotSupport]
    have hsum_eq_weight :
        (∑ a ∈ C.tailSupport, tailWeight a) =
          ∑ a ∈ C.tailSupport, C.weight a := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      have htail := (FiniteSupportCertificate.mem_tailSupport (C := C)).1 ha
      simp [tailWeight, htail.2]
    calc
      (∑' a, (if a ∈ C.finitePrefix then 0 else C.weight a)) =
          ∑ a ∈ C.tailSupport, tailWeight a := by
        simpa [tailWeight] using tsum_eq_sum (s := C.tailSupport) hzero
      _ = ∑ a ∈ C.tailSupport, C.weight a := hsum_eq_weight
      _ ≤ C.tailBound := C.tail_sum_le_bound

end FiniteSupportCertificate
end TailSummability
end Exact3D
end StatMech
