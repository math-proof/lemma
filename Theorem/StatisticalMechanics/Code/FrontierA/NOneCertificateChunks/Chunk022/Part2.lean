/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk022.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk022.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts45_checked :
    rawMomentVCounts 45 = generatedVCounts45 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts45_checked :
    rawMomentQCounts 45 = generatedQCounts45 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients45_checked :
    rawMomentStateCoefficientList 45 = generatedStateCoefficients45 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts45_checked, qCounts45_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
