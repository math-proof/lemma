/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk215.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk215


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts430_checked :
    rawMomentVCounts 430 = generatedVCounts430 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts430_checked :
    rawMomentQCounts 430 = generatedQCounts430 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients430_checked :
    rawMomentStateCoefficientList 430 = generatedStateCoefficients430 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts430_checked, qCounts430_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
