/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk066.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk066


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts132_checked :
    rawMomentVCounts 132 = generatedVCounts132 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts132_checked :
    rawMomentQCounts 132 = generatedQCounts132 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients132_checked :
    rawMomentStateCoefficientList 132 = generatedStateCoefficients132 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts132_checked, qCounts132_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
