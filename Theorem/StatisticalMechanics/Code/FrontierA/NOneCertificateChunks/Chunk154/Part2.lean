/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk154.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk154.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts309_checked :
    rawMomentVCounts 309 = generatedVCounts309 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts309_checked :
    rawMomentQCounts 309 = generatedQCounts309 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients309_checked :
    rawMomentStateCoefficientList 309 = generatedStateCoefficients309 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts309_checked, qCounts309_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
