/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk145.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk145.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts291_checked :
    rawMomentVCounts 291 = generatedVCounts291 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts291_checked :
    rawMomentQCounts 291 = generatedQCounts291 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients291_checked :
    rawMomentStateCoefficientList 291 = generatedStateCoefficients291 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts291_checked, qCounts291_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
