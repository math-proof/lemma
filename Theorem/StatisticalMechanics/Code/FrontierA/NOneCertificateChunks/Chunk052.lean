/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk052.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk052


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts104_checked :
    rawMomentVCounts 104 = generatedVCounts104 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts104_checked :
    rawMomentQCounts 104 = generatedQCounts104 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients104_checked :
    rawMomentStateCoefficientList 104 = generatedStateCoefficients104 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts104_checked, qCounts104_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
