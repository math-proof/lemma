/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificateExample.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyTailBridgeExample

noncomputable def rawRows_indicatorTail_finiteSupportCertificate {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffStableKey
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (support.card : ℝ) * ((1 : ℝ) / 10))
    K (indicatorTailSplit (d := d) K support)
    (StableKeyCertificateExample.rawRows d K.radius K.maxDegree K.maxRange)
    StableKeyCertificateExample.zeroInterval (fun _ => (0 : ℝ)) support ∅
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    (indicatorTailSplit_total_zero_off_support K support)
    (indicatorTailSplit_total_nonneg K support)
    (indicatorTailSplit_additive K support)
    (StableKeyCertificateExample.rawRows_cover d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_finiteContribution_eq_zero K support)
    (StableKeyCertificateExample.rawRows_row_sound d K.radius K.maxDegree K.maxRange)
    (rawRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_tailEnvelopeOn K support)
    (by
      simp [Finset.sum_const, nsmul_eq_mul])


noncomputable def rawRows_indicatorTail_finiteSupportCertificate_exactKeySet
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffStableKey_exactKeySet
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (support.card : ℝ) * ((1 : ℝ) / 10))
    K (indicatorTailSplit (d := d) K support)
    (StableKeyCertificateExample.rawRows d K.radius K.maxDegree K.maxRange)
    StableKeyCertificateExample.zeroInterval
    ((exhaustiveTable d K.radius K.maxDegree K.maxRange).image stableKey)
    (fun _ => (0 : ℝ)) support ∅
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    (indicatorTailSplit_total_zero_off_support K support)
    (indicatorTailSplit_total_nonneg K support)
    (indicatorTailSplit_additive K support)
    (StableKeyCertificateExample.rawRows_exactKeySet
      d K.radius K.maxDegree K.maxRange)
    (fun c =>
      Finset.mem_image.mpr
        ⟨c, exhaustiveTable_covers d K.radius K.maxDegree K.maxRange c, rfl⟩)
    (indicatorTailSplit_finiteContribution_eq_zero K support)
    (StableKeyCertificateExample.rawRows_row_sound
      d K.radius K.maxDegree K.maxRange)
    (rawRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_tailEnvelopeOn K support)
    (by
      simp [Finset.sum_const, nsmul_eq_mul])


noncomputable def minimalCubicRows_indicatorTail_finiteSupportCertificate {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (support.card : ℝ) * ((1 : ℝ) / 10))
    K (indicatorTailSplit (d := d) K support)
    (StableKeyCertificateExample.minimalCubicRows d K.radius K.maxDegree K.maxRange)
    StableKeyCertificateExample.zeroInterval (fun _ => (0 : ℝ)) support ∅
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    (indicatorTailSplit_total_zero_off_support K support)
    (indicatorTailSplit_total_nonneg K support)
    (indicatorTailSplit_additive K support)
    (StableKeyCertificateExample.minimalCubicRows_cover d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_finiteContribution_eq_zero K support)
    (StableKeyCertificateExample.minimalCubicRows_row_sound d K.radius K.maxDegree K.maxRange)
    (minimalCubicRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_tailEnvelopeOn K support)
    (by
      simp [Finset.sum_const, nsmul_eq_mul])

end StableKeyTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
