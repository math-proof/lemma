/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk135.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk135.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts271_checked :
    rawMomentVCounts 271 = generatedVCounts271 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts271_checked :
    rawMomentQCounts 271 = generatedQCounts271 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients271_checked :
    rawMomentStateCoefficientList 271 = generatedStateCoefficients271 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts271_checked, qCounts271_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
