/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk013.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk013


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts26_checked :
    rawMomentVCounts 26 = generatedVCounts26 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts26_checked :
    rawMomentQCounts 26 = generatedQCounts26 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients26_checked :
    rawMomentStateCoefficientList 26 = generatedStateCoefficients26 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts26_checked, qCounts26_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
