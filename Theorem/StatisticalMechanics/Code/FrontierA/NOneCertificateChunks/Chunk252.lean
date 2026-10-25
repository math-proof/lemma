/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk252.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk252


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts504_checked :
    rawMomentVCounts 504 = generatedVCounts504 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts504_checked :
    rawMomentQCounts 504 = generatedQCounts504 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients504_checked :
    rawMomentStateCoefficientList 504 = generatedStateCoefficients504 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts504_checked, qCounts504_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
