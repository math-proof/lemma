/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk197.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk197


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts394_checked :
    rawMomentVCounts 394 = generatedVCounts394 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts394_checked :
    rawMomentQCounts 394 = generatedQCounts394 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients394_checked :
    rawMomentStateCoefficientList 394 = generatedStateCoefficients394 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts394_checked, qCounts394_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
