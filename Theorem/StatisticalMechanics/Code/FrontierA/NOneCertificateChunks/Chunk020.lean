/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk020.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk020


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts40_checked :
    rawMomentVCounts 40 = generatedVCounts40 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts40_checked :
    rawMomentQCounts 40 = generatedQCounts40 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients40_checked :
    rawMomentStateCoefficientList 40 = generatedStateCoefficients40 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts40_checked, qCounts40_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
