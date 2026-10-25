/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk229.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk229


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts458_checked :
    rawMomentVCounts 458 = generatedVCounts458 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts458_checked :
    rawMomentQCounts 458 = generatedQCounts458 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients458_checked :
    rawMomentStateCoefficientList 458 = generatedStateCoefficients458 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts458_checked, qCounts458_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
