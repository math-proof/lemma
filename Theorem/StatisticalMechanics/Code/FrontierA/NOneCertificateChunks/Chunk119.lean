/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk119.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk119


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts238_checked :
    rawMomentVCounts 238 = generatedVCounts238 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts238_checked :
    rawMomentQCounts 238 = generatedQCounts238 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients238_checked :
    rawMomentStateCoefficientList 238 = generatedStateCoefficients238 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts238_checked, qCounts238_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
