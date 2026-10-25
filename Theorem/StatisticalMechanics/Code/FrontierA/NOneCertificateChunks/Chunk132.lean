/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk132.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk132


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts264_checked :
    rawMomentVCounts 264 = generatedVCounts264 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts264_checked :
    rawMomentQCounts 264 = generatedQCounts264 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients264_checked :
    rawMomentStateCoefficientList 264 = generatedStateCoefficients264 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts264_checked, qCounts264_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
