/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk152.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk152.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts305_checked :
    rawMomentVCounts 305 = generatedVCounts305 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts305_checked :
    rawMomentQCounts 305 = generatedQCounts305 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients305_checked :
    rawMomentStateCoefficientList 305 = generatedStateCoefficients305 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts305_checked, qCounts305_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
