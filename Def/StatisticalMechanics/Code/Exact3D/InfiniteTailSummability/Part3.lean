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
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]


namespace InfiniteTailCertificate

variable (C : InfiniteTailCertificate α)


noncomputable def of_tailEnvelope
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_tailEnvelope : Summable tailEnvelope)
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
    InfiniteTailCertificate α where
  finitePrefix := finitePrefix
  weight := weight
  prefixWeight := fun a => if a ∈ finitePrefix then weight a else 0
  tailWeight := fun a => if a ∈ finitePrefix then 0 else weight a
  tailBound := tailBound
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
    by_cases ha : a ∈ finitePrefix <;> simp [ha]
  prefixWeight_nonneg := by
    intro a
    by_cases ha : a ∈ finitePrefix
    · simpa [ha] using hweight_nonneg a
    · simp [ha]
  tailWeight_nonneg := by
    intro a
    by_cases ha : a ∈ finitePrefix
    · simp [ha]
    · simpa [ha] using hweight_nonneg a
  summable_tail := by
    let tailWeight : α → ℝ :=
      fun a => if a ∈ finitePrefix then 0 else weight a
    have htail_nonneg : ∀ a, 0 ≤ tailWeight a := by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simp [tailWeight, ha]
      · simpa [tailWeight, ha] using hweight_nonneg a
    have htail_le : ∀ a, tailWeight a ≤ tailEnvelope a := by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simpa [tailWeight, ha] using henvelope_nonneg a
      · simpa [tailWeight, ha] using hweight_le_tailEnvelope a ha
    simpa [tailWeight] using
      Summable.of_nonneg_of_le htail_nonneg htail_le hsummable_tailEnvelope
  tail_tsum_le := by
    let tailWeight : α → ℝ :=
      fun a => if a ∈ finitePrefix then 0 else weight a
    have htail_nonneg : ∀ a, 0 ≤ tailWeight a := by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simp [tailWeight, ha]
      · simpa [tailWeight, ha] using hweight_nonneg a
    have htail_le : ∀ a, tailWeight a ≤ tailEnvelope a := by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simpa [tailWeight, ha] using henvelope_nonneg a
      · simpa [tailWeight, ha] using hweight_le_tailEnvelope a ha
    have htail_summable : Summable tailWeight :=
      Summable.of_nonneg_of_le htail_nonneg htail_le
        hsummable_tailEnvelope
    exact le_trans
      (by
        simpa [tailWeight] using
          Summable.tsum_le_tsum htail_le htail_summable
            hsummable_tailEnvelope)
      htailEnvelope_tsum_le


noncomputable def of_masked_tailEnvelope
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    InfiniteTailCertificate α :=
  of_tailEnvelope
    finitePrefix
    weight
    (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a)
    hweight_nonneg
    (by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simp [ha]
      · simpa [ha] using henvelope_nonneg_off a ha)
    (by
      intro a ha
      simpa [ha] using hweight_le_tailEnvelope a ha)
    hsummable_masked
    hmasked_tsum_le

end InfiniteTailCertificate
end TailSummability
end Exact3D
end StatMech
