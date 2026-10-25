/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk131.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk131


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts262_checked :
    rawMomentVCounts 262 = generatedVCounts262 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts262_checked :
    rawMomentQCounts 262 = generatedQCounts262 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients262_checked :
    rawMomentStateCoefficientList 262 = generatedStateCoefficients262 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts262_checked, qCounts262_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
