/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk036.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk036


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts72_checked :
    rawMomentVCounts 72 = generatedVCounts72 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts72_checked :
    rawMomentQCounts 72 = generatedQCounts72 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients72_checked :
    rawMomentStateCoefficientList 72 = generatedStateCoefficients72 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts72_checked, qCounts72_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
