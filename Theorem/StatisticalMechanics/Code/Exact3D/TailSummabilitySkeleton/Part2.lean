/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Def.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*}


variable [DecidableEq α]


namespace FiniteSupportCertificate

variable (C : FiniteSupportCertificate α)


@[simp] theorem mem_tailSupport {a : α} :
    a ∈ C.tailSupport ↔ a ∈ C.support ∧ a ∉ C.finitePrefix := by
  simp [tailSupport]


theorem summable_weight : Summable C.weight :=
  summable_of_ne_finset_zero (s := C.support) C.zero_off_support


theorem hasSum_weight :
    HasSum C.weight (∑ a ∈ C.support, C.weight a) :=
  hasSum_sum_of_ne_finset_zero (s := C.support) C.zero_off_support


theorem tsum_eq_support_sum :
    (∑' a, C.weight a) = ∑ a ∈ C.support, C.weight a :=
  tsum_eq_sum (s := C.support) C.zero_off_support


theorem support_sum_eq_prefix_add_tail :
    (∑ a ∈ C.support, C.weight a) =
      (∑ a ∈ C.finitePrefix, C.weight a) +
        ∑ a ∈ C.tailSupport, C.weight a := by
  simpa [tailSupport] using
    sum_eq_prefix_add_tail C.finitePrefix_subset_support C.weight


theorem tsum_eq_prefix_add_tail :
    (∑' a, C.weight a) =
      (∑ a ∈ C.finitePrefix, C.weight a) +
        ∑ a ∈ C.tailSupport, C.weight a := by
  rw [C.tsum_eq_support_sum, C.support_sum_eq_prefix_add_tail]


theorem prefix_sum_nonneg :
    0 ≤ ∑ a ∈ C.finitePrefix, C.weight a :=
  sum_nonneg_on fun a _ => C.weight_nonneg a


theorem tail_sum_nonneg :
    0 ≤ ∑ a ∈ C.tailSupport, C.weight a := by
  simpa [tailSupport] using
    StatMech.Exact3D.TailSummability.tail_sum_nonneg
      (s := C.support) (front := C.finitePrefix)
      (f := C.weight)
      (fun a _ _ => C.weight_nonneg a)


theorem tsum_nonneg :
    0 ≤ ∑' a, C.weight a := by
  rw [C.tsum_eq_prefix_add_tail]
  exact add_nonneg C.prefix_sum_nonneg C.tail_sum_nonneg


theorem envelope_tail_sum_nonneg :
    0 ≤ ∑ a ∈ C.tailSupport, C.envelope a := by
  simpa [tailSupport] using
    StatMech.Exact3D.TailSummability.tail_sum_nonneg
      (s := C.support) (front := C.finitePrefix)
      (f := C.envelope)
      C.envelope_nonneg_on_tail


theorem tail_sum_le_envelope_sum :
    (∑ a ∈ C.tailSupport, C.weight a) ≤
      ∑ a ∈ C.tailSupport, C.envelope a := by
  simpa [tailSupport] using
    StatMech.Exact3D.TailSummability.tail_sum_le_envelope_sum
      (s := C.support) (front := C.finitePrefix)
      (f := C.weight) (envelope := C.envelope)
      C.weight_le_envelope_on_tail


theorem tail_sum_le_bound :
    (∑ a ∈ C.tailSupport, C.weight a) ≤ C.tailBound :=
  le_trans C.tail_sum_le_envelope_sum <| by
    simpa [tailSupport] using C.envelope_tail_sum_le


theorem tailBound_nonneg : 0 ≤ C.tailBound :=
  le_trans C.envelope_tail_sum_nonneg <| by
    simpa [tailSupport] using C.envelope_tail_sum_le


end FiniteSupportCertificate
end TailSummability
end Exact3D
end StatMech
