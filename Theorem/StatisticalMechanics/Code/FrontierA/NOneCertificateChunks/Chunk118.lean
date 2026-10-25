/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk118.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk118


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts236_checked :
    rawMomentVCounts 236 = generatedVCounts236 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts236_checked :
    rawMomentQCounts 236 = generatedQCounts236 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients236_checked :
    rawMomentStateCoefficientList 236 = generatedStateCoefficients236 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts236_checked, qCounts236_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
