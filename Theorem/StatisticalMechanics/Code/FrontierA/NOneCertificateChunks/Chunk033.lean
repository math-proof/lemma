/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk033.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk033


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts66_checked :
    rawMomentVCounts 66 = generatedVCounts66 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts66_checked :
    rawMomentQCounts 66 = generatedQCounts66 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients66_checked :
    rawMomentStateCoefficientList 66 = generatedStateCoefficients66 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts66_checked, qCounts66_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
