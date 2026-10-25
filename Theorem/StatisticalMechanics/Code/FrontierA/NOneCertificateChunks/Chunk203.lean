/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk203.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk203


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts406_checked :
    rawMomentVCounts 406 = generatedVCounts406 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts406_checked :
    rawMomentQCounts 406 = generatedQCounts406 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients406_checked :
    rawMomentStateCoefficientList 406 = generatedStateCoefficients406 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts406_checked, qCounts406_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
