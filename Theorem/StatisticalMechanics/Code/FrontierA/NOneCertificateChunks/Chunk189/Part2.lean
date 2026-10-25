/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk189.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk189.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts379_checked :
    rawMomentVCounts 379 = generatedVCounts379 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts379_checked :
    rawMomentQCounts 379 = generatedQCounts379 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients379_checked :
    rawMomentStateCoefficientList 379 = generatedStateCoefficients379 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts379_checked, qCounts379_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
