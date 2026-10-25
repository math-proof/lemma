/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk110.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk110


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts220_checked :
    rawMomentVCounts 220 = generatedVCounts220 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts220_checked :
    rawMomentQCounts 220 = generatedQCounts220 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients220_checked :
    rawMomentStateCoefficientList 220 = generatedStateCoefficients220 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts220_checked, qCounts220_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
