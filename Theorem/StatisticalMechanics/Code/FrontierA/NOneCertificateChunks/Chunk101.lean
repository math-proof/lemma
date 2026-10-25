/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk101.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk101


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts202_checked :
    rawMomentVCounts 202 = generatedVCounts202 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts202_checked :
    rawMomentQCounts 202 = generatedQCounts202 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients202_checked :
    rawMomentStateCoefficientList 202 = generatedStateCoefficients202 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts202_checked, qCounts202_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
