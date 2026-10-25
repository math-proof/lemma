/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk058.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk058


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts116_checked :
    rawMomentVCounts 116 = generatedVCounts116 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts116_checked :
    rawMomentQCounts 116 = generatedQCounts116 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients116_checked :
    rawMomentStateCoefficientList 116 = generatedStateCoefficients116 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts116_checked, qCounts116_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
