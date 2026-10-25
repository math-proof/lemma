/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk237.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk237


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts474_checked :
    rawMomentVCounts 474 = generatedVCounts474 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts474_checked :
    rawMomentQCounts 474 = generatedQCounts474 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients474_checked :
    rawMomentStateCoefficientList 474 = generatedStateCoefficients474 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts474_checked, qCounts474_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
