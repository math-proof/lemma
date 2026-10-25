/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk152.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk152


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts304_checked :
    rawMomentVCounts 304 = generatedVCounts304 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts304_checked :
    rawMomentQCounts 304 = generatedQCounts304 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients304_checked :
    rawMomentStateCoefficientList 304 = generatedStateCoefficients304 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts304_checked, qCounts304_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
