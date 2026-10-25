/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk010.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk010


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts20_checked :
    rawMomentVCounts 20 = generatedVCounts20 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts20_checked :
    rawMomentQCounts 20 = generatedQCounts20 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients20_checked :
    rawMomentStateCoefficientList 20 = generatedStateCoefficients20 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts20_checked, qCounts20_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
