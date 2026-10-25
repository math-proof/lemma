/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk150.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk150


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts300_checked :
    rawMomentVCounts 300 = generatedVCounts300 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts300_checked :
    rawMomentQCounts 300 = generatedQCounts300 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients300_checked :
    rawMomentStateCoefficientList 300 = generatedStateCoefficients300 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts300_checked, qCounts300_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
