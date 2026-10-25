/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part10
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem with_larger_finiteBound_finiteBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).finiteBound = finiteBound' :=
  rfl

@[simp] theorem with_larger_finiteBound_prefixTailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).prefixTailBound =
      W.prefixTailBound :=
  rfl

@[simp] theorem with_larger_finiteBound_tailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailBound = W.tailBound :=
  rfl

@[simp] theorem with_larger_finiteBound_tailBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailBudget = W.tailBudget :=
  rfl

@[simp] theorem with_larger_finiteBound_tableCertifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * finiteBound' +
        W.prefixTailBound + W.tailBound :=
  rfl

@[simp] theorem with_larger_finiteBound_tableFiniteBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tableFiniteBudget =
      (W.finitePrefix.card : ℝ) * finiteBound' :=
  rfl

@[simp] theorem with_larger_finiteBound_tablePrefixBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tablePrefixBudget =
      (W.finitePrefix.card : ℝ) * finiteBound' + W.prefixTailBound :=
  rfl

@[simp] theorem with_larger_finiteBound_toWitnessPackage
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).toWitnessPackage =
      W.toWitnessPackage :=
  rfl

@[simp] theorem with_larger_finiteBound_certificate
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).certificate = W.certificate :=
  rfl

@[simp] theorem with_larger_finiteBound_tailContribution
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_larger_finiteBound_tailPrefixSum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailPrefixSum =
      W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_finiteBound_tailCertifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound :=
  rfl

@[simp] theorem with_larger_finiteBound_tailTotalTsum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_finiteBound_tailRemainderSum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl


theorem with_larger_finiteBound_rgToExponentBridge
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_finiteBound hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_larger_finiteBound_valid
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_finiteBound hle).certificate.Valid correlationLength := by
  simpa using hvalid


theorem with_larger_finiteBound_hasCriticalNu
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_finiteBound hle).certificate.predictedExponent := by
  simpa using hν


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
