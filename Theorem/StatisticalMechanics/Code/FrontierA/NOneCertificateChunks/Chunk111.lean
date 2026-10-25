/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk111.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk111


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts222_checked :
    rawMomentVCounts 222 = generatedVCounts222 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts222_checked :
    rawMomentQCounts 222 = generatedQCounts222 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients222_checked :
    rawMomentStateCoefficientList 222 = generatedStateCoefficients222 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts222_checked, qCounts222_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
