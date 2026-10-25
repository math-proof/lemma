/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk040.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk040


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts80_checked :
    rawMomentVCounts 80 = generatedVCounts80 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts80_checked :
    rawMomentQCounts 80 = generatedQCounts80 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients80_checked :
    rawMomentStateCoefficientList 80 = generatedStateCoefficients80 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts80_checked, qCounts80_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
