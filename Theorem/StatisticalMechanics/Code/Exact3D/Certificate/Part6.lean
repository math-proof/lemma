/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Structure.StatisticalMechanics.Code.Exact3D.Certificate.Part2


namespace StatMech

namespace Exact3D

namespace RGCertificate

theorem hasCriticalNu_of_checks {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (_hfinite : FiniteCaseChecks C) (_htail : TailBounds C)
    (_hfixed : FixedPointEnclosure C)
    (_hlinear : LinearizationEnclosure C)
    (_hhyperbolic : HyperbolicSplitting C)
    (_horbit : OrbitEntry C)
    (hbridge : RGToExponentBridge C correlationLength) :
    HasCriticalNu M correlationLength C.predictedExponent :=
  hbridge


theorem valid_of_bridge {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hfinite : FiniteCaseChecks C) (htail : TailBounds C)
    (hfixed : FixedPointEnclosure C)
    (hlinear : LinearizationEnclosure C)
    (hhyperbolic : HyperbolicSplitting C)
    (horbit : OrbitEntry C)
    (hbridge : RGToExponentBridge C correlationLength) :
    C.Valid correlationLength where
  finiteCaseChecks := hfinite
  tailBounds := htail
  fixedPointEnclosure := hfixed
  linearizationEnclosure := hlinear
  hyperbolicSplitting := hhyperbolic
  orbitEntry := horbit
  bridge := hbridge


theorem valid_of_bridge_congr_predictedExponent {ι : Type*}
    {M : CriticalModel ι}
    (C : RGCertificate M) {D : RGCertificate M}
    (correlationLength : ℝ → ℝ)
    (hfinite : FiniteCaseChecks C) (htail : TailBounds C)
    (hfixed : FixedPointEnclosure C)
    (hlinear : LinearizationEnclosure C)
    (hhyperbolic : HyperbolicSplitting C)
    (horbit : OrbitEntry C)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (rgToExponentBridge_congr_predictedExponent hbridge hpred)


theorem bridge_of_hasCriticalNu {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hν : HasCriticalNu M correlationLength C.predictedExponent) :
    RGToExponentBridge C correlationLength := by
  simpa [RGToExponentBridge] using hν


theorem valid_of_hasCriticalNu {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hfinite : FiniteCaseChecks C) (htail : TailBounds C)
    (hfixed : FixedPointEnclosure C)
    (hlinear : LinearizationEnclosure C)
    (hhyperbolic : HyperbolicSplitting C)
    (horbit : OrbitEntry C)
    (hν : HasCriticalNu M correlationLength C.predictedExponent) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit (C.bridge_of_hasCriticalNu correlationLength hν)


theorem Valid.hasCriticalNu {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hC : C.Valid correlationLength) :
    HasCriticalNu M correlationLength C.predictedExponent :=
  hasCriticalNu_of_checks C correlationLength
    hC.finiteCaseChecks hC.tailBounds hC.fixedPointEnclosure
    hC.linearizationEnclosure hC.hyperbolicSplitting hC.orbitEntry hC.bridge


theorem rgToExponentBridge_congr_eventually {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : C.RGToExponentBridge correlationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    C.RGToExponentBridge comparisonLength :=
  hbridge.congr_eventually hEq


theorem rgToExponentBridge_congr_eventually_iff {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    C.RGToExponentBridge correlationLength ↔
      C.RGToExponentBridge comparisonLength :=
  ⟨fun hbridge => rgToExponentBridge_congr_eventually hbridge hEq,
    fun hbridge => rgToExponentBridge_congr_eventually hbridge
      (hEq.mono (fun _ hβ => hβ.symm))⟩


theorem retarget_rgToExponentBridge {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hbridge : C.RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (C.retarget N).RGToExponentBridge correlationLength := by
  simpa [RGToExponentBridge] using hbridge.congr_betaC hβc


theorem retarget_rgToExponentBridge_iff {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    C.RGToExponentBridge correlationLength ↔
      (C.retarget N).RGToExponentBridge correlationLength :=
  ⟨fun hbridge => retarget_rgToExponentBridge hbridge hβc,
    fun hbridge => by
      have hback :
          ((C.retarget N).retarget M).RGToExponentBridge correlationLength :=
        retarget_rgToExponentBridge hbridge hβc.symm
      simpa [RGToExponentBridge, retarget] using hback⟩


theorem retarget_hasCriticalNu {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hν : HasCriticalNu M correlationLength C.predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength (C.retarget N).predictedExponent := by
  simpa using hν.congr_betaC hβc


theorem retarget_hasCriticalNu_iff {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength C.predictedExponent ↔
      HasCriticalNu N correlationLength (C.retarget N).predictedExponent := by
  simpa using
    (HasCriticalNu.congr_betaC_iff
      (M := M) (N := N) (correlationLength := correlationLength)
      (ν := C.predictedExponent) hβc)


theorem Valid.congr_eventually {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength comparisonLength : ℝ → ℝ}
    (hC : C.Valid correlationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    C.Valid comparisonLength where
  finiteCaseChecks := hC.finiteCaseChecks
  tailBounds := hC.tailBounds
  fixedPointEnclosure := hC.fixedPointEnclosure
  linearizationEnclosure := hC.linearizationEnclosure
  hyperbolicSplitting := hC.hyperbolicSplitting
  orbitEntry := hC.orbitEntry
  bridge := rgToExponentBridge_congr_eventually hC.bridge hEq


theorem Valid.congr_eventually_iff {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength comparisonLength : ℝ → ℝ}
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    C.Valid correlationLength ↔ C.Valid comparisonLength :=
  ⟨fun hC => hC.congr_eventually hEq,
    fun hC => hC.congr_eventually
      (hEq.mono (fun _ hβ => hβ.symm))⟩


theorem Valid.retarget {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hC : C.Valid correlationLength) (hβc : M.betaC = N.betaC) :
    (C.retarget N).Valid correlationLength where
  finiteCaseChecks := trivial
  tailBounds := trivial
  fixedPointEnclosure := by
    simpa [retarget, FixedPointEnclosure] using hC.fixedPointEnclosure
  linearizationEnclosure := (C.retarget N).linearizationEnclosure_of_thermal_gt_one
  hyperbolicSplitting := (C.retarget N).hyperbolicSplitting_of_thermal_gt_one
  orbitEntry := trivial
  bridge := retarget_rgToExponentBridge hC.bridge hβc


theorem Valid.retarget_iff {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    C.Valid correlationLength ↔ (C.retarget N).Valid correlationLength :=
  ⟨fun hC => hC.retarget hβc,
    fun hC => by
      have hback :
          ((C.retarget N).retarget M).Valid correlationLength :=
        hC.retarget hβc.symm
      simpa [retarget, Valid, FixedPointEnclosure] using hback⟩

end RGCertificate
end Exact3D
end StatMech
