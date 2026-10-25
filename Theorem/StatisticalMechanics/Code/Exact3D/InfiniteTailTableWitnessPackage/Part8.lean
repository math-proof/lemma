/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part9
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem with_zero_tailEnvelope_and_budgets_finiteBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_prefixTailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).prefixTailBound =
      prefixTailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailBound =
      tailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailBudget =
      tailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailPrefixSum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailCertifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailEnvelope
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailEnvelope =
      (fun _ => (0 : ℝ)) :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * W.finiteBound +
        prefixTailBound' + tailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tableFiniteBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tablePrefixBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tablePrefixBudget =
      W.tableFiniteBudget + prefixTailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailContribution
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailRemainderSum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailRemainderSum =
      W.tailRemainderSum :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailTotalTsum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_certificate
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).certificate = W.certificate :=
  rfl


theorem with_zero_tailEnvelope_and_budgets_rgToExponentBridge
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge


theorem with_zero_tailEnvelope_and_budgets_valid
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).certificate.Valid
        correlationLength := by
  simpa using hvalid


theorem with_zero_tailEnvelope_and_budgets_hasCriticalNu
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
        htail_nonpos htailBound_nonneg).certificate.predictedExponent := by
  simpa using hν

@[simp] theorem with_tailEnvelope_and_budgets_finiteBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_prefixTailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).prefixTailBound = prefixTailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tailBound = tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailEnvelope
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tailEnvelope = tailEnvelope' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailPrefixSum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailCertifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailTotalTsum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tailTotalTsum = W.tailTotalTsum :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailContribution
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tailContribution = W.tailContribution :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailRemainderSum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tailRemainderSum = W.tailRemainderSum :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tableFiniteBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tablePrefixBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tablePrefixBudget =
      W.tableFiniteBudget + prefixTailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tableCertifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * W.finiteBound +
        prefixTailBound' + tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_certificate
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).certificate = W.certificate :=
  rfl


theorem with_tailEnvelope_and_budgets_rgToExponentBridge
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge


theorem with_tailEnvelope_and_budgets_valid
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
      hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).certificate.Valid correlationLength := by
  simpa using hvalid


theorem with_tailEnvelope_and_budgets_hasCriticalNu
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_tailEnvelope : Summable tailEnvelope')
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope' a) ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix
        hprefixSum henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
        htailEnvelope_tsum_le).certificate.predictedExponent := by
  simpa using hν


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
