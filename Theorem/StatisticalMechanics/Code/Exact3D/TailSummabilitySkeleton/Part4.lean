/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Def.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*}


variable [DecidableEq α]


namespace FiniteSupportCertificate

variable (C : FiniteSupportCertificate α)


@[simp] theorem with_tailEnvelope_and_tailBound_support
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).support = C.support :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBound_finitePrefix
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).finitePrefix = C.finitePrefix :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBound_weight
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).weight = C.weight :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBound_envelope
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).envelope = envelope' :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBound_tailBound
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).tailBound = tailBound' :=
  rfl


theorem tsum_le_prefix_sum_add_tailBound :
    (∑' a, C.weight a) ≤
      (∑ a ∈ C.finitePrefix, C.weight a) + C.tailBound := by
  calc
    (∑' a, C.weight a) =
        (∑ a ∈ C.finitePrefix, C.weight a) +
          ∑ a ∈ C.tailSupport, C.weight a :=
      C.tsum_eq_prefix_add_tail
    _ ≤ (∑ a ∈ C.finitePrefix, C.weight a) + C.tailBound :=
      add_le_add (le_refl _) C.tail_sum_le_bound


theorem tsum_le_prefix_sum_add_of_tailBound_le {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (∑' a, C.weight a) ≤
      (∑ a ∈ C.finitePrefix, C.weight a) + tailBound' :=
  le_trans C.tsum_le_prefix_sum_add_tailBound (add_le_add le_rfl hle)

end FiniteSupportCertificate

end TailSummability

namespace ContributionSplit

variable {α : Type*}


theorem summable_total_of_zero_off_support (S : ContributionSplit α)
    (support : Finset α)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0) :
    Summable S.totalContribution :=
  summable_of_ne_finset_zero (s := support) hzero


theorem tsum_total_eq_sum_of_zero_off_support (S : ContributionSplit α)
    (support : Finset α)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0) :
    (∑' a, S.totalContribution a) = ∑ a ∈ support, S.totalContribution a :=
  tsum_eq_sum (s := support) hzero


theorem total_le_finiteBound_add_tailEnvelopeOn
    {Case : Type*} [DecidableEq Case]
    (S : ContributionSplit α) (support : Finset α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound : ℝ} (tailEnvelope : α → ℝ)
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    {a : α} (ha : a ∈ support) :
    S.totalContribution a ≤ finiteBound + tailEnvelope a := by
  calc
    S.totalContribution a =
        S.finiteContribution a + S.tailContribution a := hadd a
    _ ≤ finiteBound + tailEnvelope a :=
      add_le_add (finite_le_of_tableUpperBound hfinite a) (htail a ha)


end ContributionSplit
end Exact3D
end StatMech
