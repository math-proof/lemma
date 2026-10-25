/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk053.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk053


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts106_checked :
    rawMomentVCounts 106 = generatedVCounts106 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts106_checked :
    rawMomentQCounts 106 = generatedQCounts106 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients106_checked :
    rawMomentStateCoefficientList 106 = generatedStateCoefficients106 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts106_checked, qCounts106_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
