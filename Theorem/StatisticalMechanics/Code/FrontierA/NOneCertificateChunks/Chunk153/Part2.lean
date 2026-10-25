/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk153.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk153.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts307_checked :
    rawMomentVCounts 307 = generatedVCounts307 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts307_checked :
    rawMomentQCounts 307 = generatedQCounts307 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients307_checked :
    rawMomentStateCoefficientList 307 = generatedStateCoefficients307 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts307_checked, qCounts307_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
