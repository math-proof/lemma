/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk081.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk081


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts162_checked :
    rawMomentVCounts 162 = generatedVCounts162 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts162_checked :
    rawMomentQCounts 162 = generatedQCounts162 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients162_checked :
    rawMomentStateCoefficientList 162 = generatedStateCoefficients162 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts162_checked, qCounts162_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
