/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk113.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk113


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts226_checked :
    rawMomentVCounts 226 = generatedVCounts226 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts226_checked :
    rawMomentQCounts 226 = generatedQCounts226 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients226_checked :
    rawMomentStateCoefficientList 226 = generatedStateCoefficients226 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts226_checked, qCounts226_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
