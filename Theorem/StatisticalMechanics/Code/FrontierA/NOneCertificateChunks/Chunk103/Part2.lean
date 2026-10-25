/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk103.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk103.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts207_checked :
    rawMomentVCounts 207 = generatedVCounts207 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts207_checked :
    rawMomentQCounts 207 = generatedQCounts207 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients207_checked :
    rawMomentStateCoefficientList 207 = generatedStateCoefficients207 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts207_checked, qCounts207_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
