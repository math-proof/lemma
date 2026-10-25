/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk138.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk138.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts277_checked :
    rawMomentVCounts 277 = generatedVCounts277 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts277_checked :
    rawMomentQCounts 277 = generatedQCounts277 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients277_checked :
    rawMomentStateCoefficientList 277 = generatedStateCoefficients277 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts277_checked, qCounts277_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
