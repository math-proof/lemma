/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk090.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk090.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts181_checked :
    rawMomentVCounts 181 = generatedVCounts181 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts181_checked :
    rawMomentQCounts 181 = generatedQCounts181 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients181_checked :
    rawMomentStateCoefficientList 181 = generatedStateCoefficients181 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts181_checked, qCounts181_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
