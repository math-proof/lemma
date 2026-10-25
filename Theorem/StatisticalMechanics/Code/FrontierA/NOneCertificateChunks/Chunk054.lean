/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk054.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk054


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts108_checked :
    rawMomentVCounts 108 = generatedVCounts108 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts108_checked :
    rawMomentQCounts 108 = generatedQCounts108 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients108_checked :
    rawMomentStateCoefficientList 108 = generatedStateCoefficients108 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts108_checked, qCounts108_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
