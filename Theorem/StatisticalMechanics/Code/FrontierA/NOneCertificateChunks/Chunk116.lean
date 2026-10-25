/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk116.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk116


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts232_checked :
    rawMomentVCounts 232 = generatedVCounts232 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts232_checked :
    rawMomentQCounts 232 = generatedQCounts232 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients232_checked :
    rawMomentStateCoefficientList 232 = generatedStateCoefficients232 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts232_checked, qCounts232_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
