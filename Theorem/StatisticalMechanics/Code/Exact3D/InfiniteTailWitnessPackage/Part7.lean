/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part8
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


@[simp] theorem with_larger_tailBudget_tailBudget
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBudget_tailPrefixSum
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_tailBudget_tailCertifiedTotalBound
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl


@[simp] theorem with_larger_tailBudget_tailContribution
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailContribution =
      W.tailContribution :=
  rfl


@[simp] theorem with_larger_tailBudget_tailTotalTsum
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailTotalTsum =
      W.tailTotalTsum :=
  rfl


@[simp] theorem with_larger_tailBudget_tailRemainderSum
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl

@[simp] theorem with_larger_tailBudget_certificate
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).certificate = W.certificate :=
  rfl


theorem with_larger_tailBudget_rgToExponentBridge
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_tailBudget hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_larger_tailBudget_valid
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_tailBudget hle).certificate.Valid correlationLength := by
  simpa using hvalid


theorem with_larger_tailBudget_hasCriticalNu
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_tailBudget hle).certificate.predictedExponent := by
  simpa using hν


theorem stable_fixedPoint_mem
    (W : InfiniteTailWitnessPackage (α := α) M) :
    FiniteContraction.ClosedBall
      W.stable.contraction.center W.stable.contraction.radius
      W.stable.fixedPoint :=
  W.stable.fixedPoint_mem


theorem stable_exists_unique_fixedPoint
    (W : InfiniteTailWitnessPackage (α := α) M) :
    ∃! p : Fin W.nStable → ℝ, W.stable.map p = p :=
  W.stable.exists_unique_fixedPoint


theorem valid_of_bridge
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.finiteChecks.valid_of_bridge hbridge


theorem hasCriticalNu_of_bridge
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_bridge hbridge).hasCriticalNu


theorem rgToExponentBridge_of_bridge_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred


theorem valid_of_bridge_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_bridge_congr_predictedExponent hpred hbridge)


theorem hasCriticalNu_of_bridge_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_bridge_congr_predictedExponent hpred hbridge).hasCriticalNu


theorem rgToExponentBridge_of_hasCriticalNu
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.RGToExponentBridge correlationLength := by
  simpa [RGCertificate.RGToExponentBridge] using hν


theorem valid_of_hasCriticalNu
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_hasCriticalNu hν)

end InfiniteTailWitnessPackage
end Exact3D
end StatMech
