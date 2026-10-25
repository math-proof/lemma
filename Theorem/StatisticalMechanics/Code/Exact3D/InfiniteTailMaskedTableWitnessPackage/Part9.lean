/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part9
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem with_larger_tailBound_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem with_larger_tailBound_prefixTailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).prefixTailBound =
      W.prefixTailBound :=
  rfl

@[simp] theorem with_larger_tailBound_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailBound = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_tailPrefixSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_tailBound_tailCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_tableFiniteBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_larger_tailBound_tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tablePrefixBudget =
      W.tablePrefixBudget :=
  rfl

@[simp] theorem with_larger_tailBound_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * W.finiteBound +
        W.prefixTailBound + tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_larger_tailBound_tailTotalTsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailTotalTsum = W.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_tailBound_tailRemainderSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl

@[simp] theorem with_larger_tailBound_certificate
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).certificate = W.certificate :=
  rfl


theorem with_larger_tailBound_rgToExponentBridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_tailBound hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_larger_tailBound_valid
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_tailBound hle).certificate.Valid correlationLength := by
  simpa using hvalid


theorem with_larger_tailBound_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_tailBound hle).certificate.predictedExponent := by
  simpa using hν


theorem valid_of_bridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.toWitnessPackage.valid_of_bridge hbridge


theorem hasCriticalNu_of_bridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.toWitnessPackage.hasCriticalNu_of_bridge hbridge


theorem rgToExponentBridge_of_bridge_congr_predictedExponent
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.toWitnessPackage.rgToExponentBridge_of_bridge_congr_predictedExponent
    hpred hbridge


theorem valid_of_bridge_congr_predictedExponent
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_bridge_congr_predictedExponent hpred hbridge)


theorem hasCriticalNu_of_bridge_congr_predictedExponent
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.toWitnessPackage.hasCriticalNu_of_bridge_congr_predictedExponent
    hpred hbridge


theorem rgToExponentBridge_of_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.toWitnessPackage.rgToExponentBridge_of_hasCriticalNu hν


theorem valid_of_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.Valid correlationLength :=
  W.toWitnessPackage.valid_of_hasCriticalNu hν

end InfiniteTailMaskedTableWitnessPackage
end Exact3D
end StatMech
