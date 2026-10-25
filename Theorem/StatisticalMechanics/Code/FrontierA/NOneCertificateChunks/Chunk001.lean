/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk001.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk001


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts2_checked :
    rawMomentVCounts 2 = generatedVCounts2 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts2_checked :
    rawMomentQCounts 2 = generatedQCounts2 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients2_checked :
    rawMomentStateCoefficientList 2 = generatedStateCoefficients2 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts2_checked, qCounts2_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
