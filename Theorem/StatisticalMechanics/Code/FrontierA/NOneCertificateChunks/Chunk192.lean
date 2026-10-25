/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk192.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk192


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts384_checked :
    rawMomentVCounts 384 = generatedVCounts384 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts384_checked :
    rawMomentQCounts 384 = generatedQCounts384 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients384_checked :
    rawMomentStateCoefficientList 384 = generatedStateCoefficients384 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts384_checked, qCounts384_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
