/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk055.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk055


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts110_checked :
    rawMomentVCounts 110 = generatedVCounts110 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts110_checked :
    rawMomentQCounts 110 = generatedQCounts110 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients110_checked :
    rawMomentStateCoefficientList 110 = generatedStateCoefficients110 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts110_checked, qCounts110_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
