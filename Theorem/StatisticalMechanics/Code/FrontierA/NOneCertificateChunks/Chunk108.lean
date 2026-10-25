/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk108.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk108


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts216_checked :
    rawMomentVCounts 216 = generatedVCounts216 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts216_checked :
    rawMomentQCounts 216 = generatedQCounts216 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients216_checked :
    rawMomentStateCoefficientList 216 = generatedStateCoefficients216 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts216_checked, qCounts216_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
