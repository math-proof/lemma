/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk094.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk094


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts188_checked :
    rawMomentVCounts 188 = generatedVCounts188 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts188_checked :
    rawMomentQCounts 188 = generatedQCounts188 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients188_checked :
    rawMomentStateCoefficientList 188 = generatedStateCoefficients188 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts188_checked, qCounts188_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
