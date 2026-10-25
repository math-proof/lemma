/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem certificate_scale_eq
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.scale = W.scale :=
  rfl

@[simp] theorem certificate_thermalEigenvalue_eq
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.thermalEigenvalue = W.thermal :=
  rfl


theorem certificate_predictedExponent_eq
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.predictedExponent = predictedNu W.scale W.thermal :=
  rfl

@[simp] theorem retarget_certificate {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).certificate = W.certificate.retarget N :=
  rfl

@[simp] theorem retarget_finiteBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem retarget_prefixTailBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).prefixTailBound = W.prefixTailBound :=
  rfl

@[simp] theorem retarget_tailBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailBound = W.tailBound :=
  rfl


theorem retarget_rgToExponentBridge {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc


theorem retarget_valid {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.Valid correlationLength := by
  simpa using hvalid.retarget hβc


theorem retarget_hasCriticalNu {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      ((W.retarget N).certificate).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc


theorem retarget_rgToExponentBridge_iff {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    W.certificate.RGToExponentBridge correlationLength ↔
      (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := W.certificate) (N := N) hβc)


theorem retarget_valid_iff {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    W.certificate.Valid correlationLength ↔
      (W.retarget N).certificate.Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := W.certificate) (N := N) hβc)


theorem retarget_hasCriticalNu_iff {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent ↔
      HasCriticalNu N correlationLength
        ((W.retarget N).certificate).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := W.certificate) (N := N) hβc)


theorem finiteChecks
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.FiniteChecks :=
  W.toWitnessPackage.finiteChecks


theorem finiteCaseChecks
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.FiniteCaseChecks :=
  W.toWitnessPackage.finiteCaseChecks


theorem tailBounds
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.TailBounds :=
  W.toWitnessPackage.tailBounds


theorem fixedPointEnclosure
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.FixedPointEnclosure :=
  W.toWitnessPackage.fixedPointEnclosure


theorem linearizationEnclosure
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.LinearizationEnclosure :=
  W.toWitnessPackage.linearizationEnclosure


theorem hyperbolicSplitting
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.HyperbolicSplitting :=
  W.toWitnessPackage.hyperbolicSplitting


theorem orbitEntry
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.OrbitEntry :=
  W.toWitnessPackage.orbitEntry


end InfiniteTailMaskedTableWitnessPackage
end Exact3D
end StatMech
