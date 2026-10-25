/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk065.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk065.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts131_checked :
    rawMomentVCounts 131 = generatedVCounts131 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts131_checked :
    rawMomentQCounts 131 = generatedQCounts131 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients131_checked :
    rawMomentStateCoefficientList 131 = generatedStateCoefficients131 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts131_checked, qCounts131_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
