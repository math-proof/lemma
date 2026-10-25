/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Def.StatisticalMechanics.Code.Exact3D.Certificate.Part5


namespace StatMech

namespace Exact3D

namespace RGCertificate

theorem rgToExponentBridge_congr_predictedExponent {ι : Type*}
    {M : CriticalModel ι} {C D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : C.predictedExponent = D.predictedExponent) :
    C.RGToExponentBridge correlationLength := by
  unfold RGToExponentBridge at hbridge ⊢
  simpa [hpred] using hbridge


theorem rgToExponentBridge_congr_predictedExponent_iff {ι : Type*}
    {M : CriticalModel ι} {C D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent) :
    C.RGToExponentBridge correlationLength ↔
      D.RGToExponentBridge correlationLength :=
  ⟨fun hbridge =>
      rgToExponentBridge_congr_predictedExponent hbridge hpred.symm,
    fun hbridge =>
      rgToExponentBridge_congr_predictedExponent hbridge hpred⟩


theorem retarget_rgToExponentBridge_of_hasCriticalNu {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hν : HasCriticalNu N correlationLength C.predictedExponent) :
    (C.retarget N).RGToExponentBridge correlationLength := by
  simpa [RGToExponentBridge] using hν


end RGCertificate
end Exact3D
end StatMech
