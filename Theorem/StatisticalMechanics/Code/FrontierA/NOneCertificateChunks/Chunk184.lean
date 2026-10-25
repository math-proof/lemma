/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk184.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk184


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts368_checked :
    rawMomentVCounts 368 = generatedVCounts368 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts368_checked :
    rawMomentQCounts 368 = generatedQCounts368 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients368_checked :
    rawMomentStateCoefficientList 368 = generatedStateCoefficients368 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts368_checked, qCounts368_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
