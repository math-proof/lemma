/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk148.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk148


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts296_checked :
    rawMomentVCounts 296 = generatedVCounts296 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts296_checked :
    rawMomentQCounts 296 = generatedQCounts296 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients296_checked :
    rawMomentStateCoefficientList 296 = generatedStateCoefficients296 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts296_checked, qCounts296_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
