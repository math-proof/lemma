/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk060.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk060.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts121_checked :
    rawMomentVCounts 121 = generatedVCounts121 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts121_checked :
    rawMomentQCounts 121 = generatedQCounts121 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients121_checked :
    rawMomentStateCoefficientList 121 = generatedStateCoefficients121 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts121_checked, qCounts121_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
