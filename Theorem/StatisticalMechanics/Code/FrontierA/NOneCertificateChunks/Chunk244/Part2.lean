/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk244.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk244.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts489_checked :
    rawMomentVCounts 489 = generatedVCounts489 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts489_checked :
    rawMomentQCounts 489 = generatedQCounts489 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients489_checked :
    rawMomentStateCoefficientList 489 = generatedStateCoefficients489 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts489_checked, qCounts489_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
