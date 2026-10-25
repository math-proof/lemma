/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk104.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk104


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts208_checked :
    rawMomentVCounts 208 = generatedVCounts208 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts208_checked :
    rawMomentQCounts 208 = generatedQCounts208 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients208_checked :
    rawMomentStateCoefficientList 208 = generatedStateCoefficients208 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts208_checked, qCounts208_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
