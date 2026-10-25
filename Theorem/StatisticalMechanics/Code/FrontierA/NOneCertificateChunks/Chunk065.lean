/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk065.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk065


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts130_checked :
    rawMomentVCounts 130 = generatedVCounts130 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts130_checked :
    rawMomentQCounts 130 = generatedQCounts130 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients130_checked :
    rawMomentStateCoefficientList 130 = generatedStateCoefficients130 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts130_checked, qCounts130_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
