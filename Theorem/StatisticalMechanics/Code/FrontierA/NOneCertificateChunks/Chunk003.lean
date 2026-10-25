/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk003.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk003


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts6_checked :
    rawMomentVCounts 6 = generatedVCounts6 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts6_checked :
    rawMomentQCounts 6 = generatedQCounts6 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients6_checked :
    rawMomentStateCoefficientList 6 = generatedStateCoefficients6 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts6_checked, qCounts6_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
