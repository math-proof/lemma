/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk130.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk130


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts260_checked :
    rawMomentVCounts 260 = generatedVCounts260 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts260_checked :
    rawMomentQCounts 260 = generatedQCounts260 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients260_checked :
    rawMomentStateCoefficientList 260 = generatedStateCoefficients260 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts260_checked, qCounts260_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
