/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk235.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk235.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts471_checked :
    rawMomentVCounts 471 = generatedVCounts471 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts471_checked :
    rawMomentQCounts 471 = generatedQCounts471 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients471_checked :
    rawMomentStateCoefficientList 471 = generatedStateCoefficients471 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts471_checked, qCounts471_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
