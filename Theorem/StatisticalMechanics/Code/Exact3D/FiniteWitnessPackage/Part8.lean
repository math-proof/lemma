/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part8
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


@[simp] theorem with_tailEnvelope_and_tailBudget_tailBudget
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBudget_tailPrefixSum
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailPrefixSum =
        W.tailPrefixSum :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBudget_certificate
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).certificate =
        W.certificate :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailCertifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailCertifiedTotalBound =
        W.tailPrefixSum + tailBound' :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailContribution
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailContribution =
        W.tailContribution :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailTotalTsum
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailTotalTsum =
        W.tailTotalTsum :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailSupport
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailSupport =
        W.tailSupport :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailRemainderSum
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailRemainderSum =
        W.tailRemainderSum :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailEnvelopeSum
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailEnvelopeSum =
        ∑ a ∈ W.tailSupport, envelope' a :=
  rfl


theorem with_tailEnvelope_and_tailBudget_rgToExponentBridge
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge


theorem with_tailEnvelope_and_tailBudget_valid
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).certificate.Valid
        correlationLength := by
  simpa using hvalid


theorem with_tailEnvelope_and_tailBudget_hasCriticalNu
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_tailEnvelope_and_tailBudget envelope'
        henvelope_nonneg hweight_le henvelope_sum).certificate.predictedExponent := by
  simpa using hν


end FiniteWitnessPackage
end Exact3D
end StatMech
