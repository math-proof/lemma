/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk195.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk195


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts390_checked :
    rawMomentVCounts 390 = generatedVCounts390 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts390_checked :
    rawMomentQCounts 390 = generatedQCounts390 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients390_checked :
    rawMomentStateCoefficientList 390 = generatedStateCoefficients390 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts390_checked, qCounts390_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
