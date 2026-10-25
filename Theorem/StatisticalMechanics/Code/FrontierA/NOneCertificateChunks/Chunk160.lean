/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk160.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk160


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts320_checked :
    rawMomentVCounts 320 = generatedVCounts320 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts320_checked :
    rawMomentQCounts 320 = generatedQCounts320 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients320_checked :
    rawMomentStateCoefficientList 320 = generatedStateCoefficients320 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts320_checked, qCounts320_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
