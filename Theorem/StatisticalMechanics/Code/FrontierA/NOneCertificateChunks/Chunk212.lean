/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk212.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk212


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts424_checked :
    rawMomentVCounts 424 = generatedVCounts424 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts424_checked :
    rawMomentQCounts 424 = generatedQCounts424 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients424_checked :
    rawMomentStateCoefficientList 424 = generatedStateCoefficients424 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts424_checked, qCounts424_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
