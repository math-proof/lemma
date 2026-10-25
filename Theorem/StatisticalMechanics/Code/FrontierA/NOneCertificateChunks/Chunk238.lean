/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk238.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk238


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts476_checked :
    rawMomentVCounts 476 = generatedVCounts476 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts476_checked :
    rawMomentQCounts 476 = generatedQCounts476 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients476_checked :
    rawMomentStateCoefficientList 476 = generatedStateCoefficients476 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts476_checked, qCounts476_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
