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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]


namespace InfiniteTailCertificate

variable (C : InfiniteTailCertificate α)


@[simp] theorem of_masked_tailEnvelope_finitePrefix
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
    (of_masked_tailEnvelope finitePrefix weight tailEnvelope hweight_nonneg
      henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).finitePrefix = finitePrefix :=
  rfl

@[simp] theorem of_masked_tailEnvelope_weight
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
    (of_masked_tailEnvelope finitePrefix weight tailEnvelope hweight_nonneg
      henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).weight = weight :=
  rfl

@[simp] theorem of_masked_tailEnvelope_tailBound
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
    (of_masked_tailEnvelope finitePrefix weight tailEnvelope hweight_nonneg
      henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailBound = tailBound :=
  rfl

end InfiniteTailCertificate
end TailSummability
end Exact3D
end StatMech
