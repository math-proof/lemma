/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk136.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk136


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts272_checked :
    rawMomentVCounts 272 = generatedVCounts272 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts272_checked :
    rawMomentQCounts 272 = generatedQCounts272 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients272_checked :
    rawMomentStateCoefficientList 272 = generatedStateCoefficients272 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts272_checked, qCounts272_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
