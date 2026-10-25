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
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


@[simp] theorem with_larger_tailBudget_tailBudget
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBudget_tailPrefixSum
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_tailBudget_tailCertifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl


@[simp] theorem with_larger_tailBudget_tailContribution
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailContribution =
      W.tailContribution :=
  rfl


@[simp] theorem with_larger_tailBudget_tailTotalTsum
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailTotalTsum =
      W.tailTotalTsum :=
  rfl


@[simp] theorem with_larger_tailBudget_tailSupport
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailSupport = W.tailSupport :=
  rfl


@[simp] theorem with_larger_tailBudget_tailRemainderSum
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl


@[simp] theorem with_larger_tailBudget_tailEnvelopeSum
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailEnvelopeSum = W.tailEnvelopeSum :=
  rfl

@[simp] theorem with_larger_tailBudget_certificate
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).certificate = W.certificate :=
  rfl


theorem with_larger_tailBudget_rgToExponentBridge
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_tailBudget hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_larger_tailBudget_valid
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_tailBudget hle).certificate.Valid correlationLength := by
  simpa using hvalid


theorem with_larger_tailBudget_hasCriticalNu
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_tailBudget hle).certificate.predictedExponent := by
  simpa using hν


theorem tail_tsum_le_prefix_add_of_tailBudget_le
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (∑' a, W.tailCertificate.weight a) ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailPrefixSum, tailBudget] using
    W.tailCertificate.tsum_le_prefix_sum_add_of_tailBound_le hle


theorem tailTotalTsum_le_prefix_add_of_tailBudget_le
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailTotalTsum, tailContribution] using
    W.tail_tsum_le_prefix_add_of_tailBudget_le hle


theorem tailRemainderSum_le_of_tailBudget_le
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailRemainderSum ≤ tailBound' :=
  le_trans W.tailRemainderSum_le_tailBudget hle


theorem tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailCertifiedTotalBound] using
    add_le_add (le_refl W.tailPrefixSum) hle


theorem tailPrefixSum_nonneg (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailPrefixSum := by
  simpa [tailPrefixSum] using W.tailCertificate.prefix_sum_nonneg


theorem tailBudget_nonneg (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailBudget := by
  simpa [tailBudget] using W.tailCertificate.tailBound_nonneg


theorem tailCertifiedTotalBound_nonneg
    (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailCertifiedTotalBound :=
  add_nonneg W.tailPrefixSum_nonneg W.tailBudget_nonneg


theorem tail_tsum_nonneg (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ ∑' a, W.tailCertificate.weight a :=
  W.tailCertificate.tsum_nonneg


theorem stable_fixedPoint_mem (W : FiniteWitnessPackage (α := α) M) :
    FiniteContraction.ClosedBall
      W.stable.contraction.center W.stable.contraction.radius
      W.stable.fixedPoint :=
  W.stable.fixedPoint_mem


theorem stable_exists_unique_fixedPoint
    (W : FiniteWitnessPackage (α := α) M) :
    ∃! p : Fin W.nStable → ℝ, W.stable.map p = p :=
  W.stable.exists_unique_fixedPoint


theorem valid_of_bridge (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.finiteChecks.valid_of_bridge hbridge


theorem hasCriticalNu_of_bridge (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_bridge hbridge).hasCriticalNu


theorem rgToExponentBridge_of_bridge_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred


theorem valid_of_bridge_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_bridge_congr_predictedExponent hpred hbridge)


theorem hasCriticalNu_of_bridge_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_bridge_congr_predictedExponent hpred hbridge).hasCriticalNu


theorem rgToExponentBridge_of_hasCriticalNu
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.RGToExponentBridge correlationLength := by
  simpa [RGCertificate.RGToExponentBridge] using hν


theorem valid_of_hasCriticalNu (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_hasCriticalNu hν)

end FiniteWitnessPackage
end Exact3D
end StatMech
