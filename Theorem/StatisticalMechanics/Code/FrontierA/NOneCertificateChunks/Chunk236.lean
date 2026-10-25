/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk236.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk236


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts472_checked :
    rawMomentVCounts 472 = generatedVCounts472 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts472_checked :
    rawMomentQCounts 472 = generatedQCounts472 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients472_checked :
    rawMomentStateCoefficientList 472 = generatedStateCoefficients472 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts472_checked, qCounts472_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
