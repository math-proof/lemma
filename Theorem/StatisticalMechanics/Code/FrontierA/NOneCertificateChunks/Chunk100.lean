/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk100.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk100


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts200_checked :
    rawMomentVCounts 200 = generatedVCounts200 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts200_checked :
    rawMomentQCounts 200 = generatedQCounts200 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients200_checked :
    rawMomentStateCoefficientList 200 = generatedStateCoefficients200 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts200_checked, qCounts200_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
