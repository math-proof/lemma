/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part10


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

@[simp] theorem exactScaleObservable_eq_power {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (β : ℝ) :
    H.exactScaleObservable scale M β =
      Real.exp (-(H.certificate scale M).predictedExponent *
        Real.log (M.betaC - β)) :=
  rfl


theorem certificate_rgToExponentBridge_exactScaleObservable
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).RGToExponentBridge
      (H.exactScaleObservable scale M) := by
  refine (H.certificate scale M).rgToExponentBridge_of_exact_power_on_Ioo
    (H.exactScaleObservable scale M) 1 (by norm_num) ?_
  intro β _hβ
  exact H.exactScaleObservable_eq_power scale M β


theorem certificate_valid_exactScaleObservable {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).Valid (H.exactScaleObservable scale M) :=
  H.certificate_valid_of_bridge scale M (H.exactScaleObservable scale M)
    (H.certificate_rgToExponentBridge_exactScaleObservable scale M)


theorem certificate_hasCriticalNu_exactScaleObservable
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    HasCriticalNu M (H.exactScaleObservable scale M)
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_exactScaleObservable scale M).hasCriticalNu


theorem certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred


theorem certificate_valid_of_bridge_congr_predictedExponent
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
      scale M hpred hbridge)


theorem certificate_hasCriticalNu_of_bridge_congr_predictedExponent
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_bridge_congr_predictedExponent
    scale M hpred hbridge).hasCriticalNu


theorem certificate_retarget_rgToExponentBridge {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC)
    (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
    (H.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc


theorem certificate_retarget_valid {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC)
    (hvalid : (H.certificate scale M).Valid correlationLength) :
    (H.certificate scale N).Valid correlationLength := by
  simpa using hvalid.retarget hβc


theorem certificate_retarget_hasCriticalNu {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC)
    (hν :
      HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent) :
    HasCriticalNu N correlationLength
      (H.certificate scale N).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc


theorem certificate_retarget_rgToExponentBridge_iff
    {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    (H.certificate scale M).RGToExponentBridge correlationLength ↔
      (H.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := H.certificate scale M) (N := N) hβc)


theorem certificate_retarget_valid_iff {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    (H.certificate scale M).Valid correlationLength ↔
      (H.certificate scale N).Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := H.certificate scale M) (N := N) hβc)


theorem certificate_retarget_hasCriticalNu_iff {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent ↔
      HasCriticalNu N correlationLength
        (H.certificate scale N).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := H.certificate scale M) (N := N) hβc)

end FiniteHyperbolicSplitting
end Exact3D
end StatMech
