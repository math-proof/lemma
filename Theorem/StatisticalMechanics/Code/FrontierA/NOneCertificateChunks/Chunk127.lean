/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk127.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk127


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts254_checked :
    rawMomentVCounts 254 = generatedVCounts254 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts254_checked :
    rawMomentQCounts 254 = generatedQCounts254 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients254_checked :
    rawMomentStateCoefficientList 254 = generatedStateCoefficients254 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts254_checked, qCounts254_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
