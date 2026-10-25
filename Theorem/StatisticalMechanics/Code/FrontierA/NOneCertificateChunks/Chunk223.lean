/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk223.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk223


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts446_checked :
    rawMomentVCounts 446 = generatedVCounts446 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts446_checked :
    rawMomentQCounts 446 = generatedQCounts446 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients446_checked :
    rawMomentStateCoefficientList 446 = generatedStateCoefficients446 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts446_checked, qCounts446_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
