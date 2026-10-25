/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk017.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk017


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts34_checked :
    rawMomentVCounts 34 = generatedVCounts34 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts34_checked :
    rawMomentQCounts 34 = generatedQCounts34 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients34_checked :
    rawMomentStateCoefficientList 34 = generatedStateCoefficients34 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts34_checked, qCounts34_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
