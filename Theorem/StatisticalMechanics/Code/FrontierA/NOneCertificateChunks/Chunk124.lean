/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk124.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk124


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts248_checked :
    rawMomentVCounts 248 = generatedVCounts248 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts248_checked :
    rawMomentQCounts 248 = generatedQCounts248 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients248_checked :
    rawMomentStateCoefficientList 248 = generatedStateCoefficients248 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts248_checked, qCounts248_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
