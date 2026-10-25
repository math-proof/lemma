/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk097.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk097.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts195_checked :
    rawMomentVCounts 195 = generatedVCounts195 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts195_checked :
    rawMomentQCounts 195 = generatedQCounts195 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients195_checked :
    rawMomentStateCoefficientList 195 = generatedStateCoefficients195 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts195_checked, qCounts195_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
