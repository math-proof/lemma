/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk182.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk182.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts365_checked :
    rawMomentVCounts 365 = generatedVCounts365 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts365_checked :
    rawMomentQCounts 365 = generatedQCounts365 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients365_checked :
    rawMomentStateCoefficientList 365 = generatedStateCoefficients365 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts365_checked, qCounts365_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
