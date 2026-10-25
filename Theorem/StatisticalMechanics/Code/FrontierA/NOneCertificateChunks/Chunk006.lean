/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk006.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk006


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts12_checked :
    rawMomentVCounts 12 = generatedVCounts12 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts12_checked :
    rawMomentQCounts 12 = generatedQCounts12 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients12_checked :
    rawMomentStateCoefficientList 12 = generatedStateCoefficients12 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts12_checked, qCounts12_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
