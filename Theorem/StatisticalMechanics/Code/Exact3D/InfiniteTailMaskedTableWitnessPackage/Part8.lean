/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part8
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem with_larger_prefixTailBound_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem with_larger_prefixTailBound_prefixTailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).prefixTailBound =
      prefixTailBound' :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailBound = W.tailBound :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailBudget = W.tailBudget :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tableFiniteBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tablePrefixBudget =
      W.tableFiniteBudget + prefixTailBound' :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * W.finiteBound +
        prefixTailBound' + W.tailBound :=
  rfl

@[simp] theorem with_larger_prefixTailBound_toWitnessPackage
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).toWitnessPackage =
      W.toWitnessPackage :=
  rfl

@[simp] theorem with_larger_prefixTailBound_certificate
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).certificate = W.certificate :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailPrefixSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailPrefixSum =
      W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailTotalTsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailRemainderSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl


theorem with_larger_prefixTailBound_rgToExponentBridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_prefixTailBound hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_larger_prefixTailBound_valid
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_prefixTailBound hle).certificate.Valid
      correlationLength := by
  simpa using hvalid


theorem with_larger_prefixTailBound_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_prefixTailBound hle).certificate.predictedExponent := by
  simpa using hν


end InfiniteTailMaskedTableWitnessPackage
end Exact3D
end StatMech
