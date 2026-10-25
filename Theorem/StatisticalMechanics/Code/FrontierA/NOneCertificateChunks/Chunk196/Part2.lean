/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk196.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk196.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts393_checked :
    rawMomentVCounts 393 = generatedVCounts393 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts393_checked :
    rawMomentQCounts 393 = generatedQCounts393 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients393_checked :
    rawMomentStateCoefficientList 393 = generatedStateCoefficients393 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts393_checked, qCounts393_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
