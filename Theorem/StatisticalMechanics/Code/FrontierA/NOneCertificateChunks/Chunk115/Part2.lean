/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk115.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk115.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts231_checked :
    rawMomentVCounts 231 = generatedVCounts231 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts231_checked :
    rawMomentQCounts 231 = generatedQCounts231 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients231_checked :
    rawMomentStateCoefficientList 231 = generatedStateCoefficients231 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts231_checked, qCounts231_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
