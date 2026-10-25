/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk186.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk186


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts372_checked :
    rawMomentVCounts 372 = generatedVCounts372 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts372_checked :
    rawMomentQCounts 372 = generatedQCounts372 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients372_checked :
    rawMomentStateCoefficientList 372 = generatedStateCoefficients372 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts372_checked, qCounts372_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
