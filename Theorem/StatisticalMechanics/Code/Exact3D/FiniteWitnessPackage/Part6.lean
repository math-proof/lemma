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
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part6
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


@[simp] theorem retarget_certificate {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).certificate = W.certificate.retarget N :=
  rfl


theorem retarget_rgToExponentBridge {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc


theorem retarget_valid {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.Valid correlationLength := by
  simpa using hvalid.retarget hβc


theorem retarget_hasCriticalNu {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      ((W.retarget N).certificate).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc


theorem retarget_rgToExponentBridge_iff {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    W.certificate.RGToExponentBridge correlationLength ↔
      (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := W.certificate) (N := N) hβc)


theorem retarget_valid_iff {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    W.certificate.Valid correlationLength ↔
      (W.retarget N).certificate.Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := W.certificate) (N := N) hβc)


theorem retarget_hasCriticalNu_iff {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent ↔
      HasCriticalNu N correlationLength
        ((W.retarget N).certificate).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := W.certificate) (N := N) hβc)


theorem fixedPointEnclosure (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.FixedPointEnclosure := by
  simpa [certificate, fixedPointData, RGCertificate.FixedPointEnclosure] using
    W.fixedPoint_eq


theorem finiteChecks (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.FiniteChecks where
  finiteCaseChecks := trivial
  tailBounds := trivial
  fixedPointEnclosure := W.fixedPointEnclosure
  linearizationEnclosure := W.certificate.linearizationEnclosure_of_thermal_gt_one
  hyperbolicSplitting := W.certificate.hyperbolicSplitting_of_thermal_gt_one
  orbitEntry := trivial


theorem finiteCaseChecks (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.FiniteCaseChecks :=
  W.finiteChecks.finiteCaseChecks


theorem tailBounds (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.TailBounds :=
  W.finiteChecks.tailBounds


theorem linearizationEnclosure (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.LinearizationEnclosure :=
  W.finiteChecks.linearizationEnclosure


theorem hyperbolicSplitting (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.HyperbolicSplitting :=
  W.finiteChecks.hyperbolicSplitting


theorem orbitEntry (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.OrbitEntry :=
  W.finiteChecks.orbitEntry


end FiniteWitnessPackage
end Exact3D
end StatMech
