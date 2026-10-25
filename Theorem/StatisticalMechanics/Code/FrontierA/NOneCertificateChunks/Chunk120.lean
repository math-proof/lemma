/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk120.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk120


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts240_checked :
    rawMomentVCounts 240 = generatedVCounts240 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts240_checked :
    rawMomentQCounts 240 = generatedQCounts240 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients240_checked :
    rawMomentStateCoefficientList 240 = generatedStateCoefficients240 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts240_checked, qCounts240_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
