/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk234.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk234


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts468_checked :
    rawMomentVCounts 468 = generatedVCounts468 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts468_checked :
    rawMomentQCounts 468 = generatedQCounts468 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients468_checked :
    rawMomentStateCoefficientList 468 = generatedStateCoefficients468 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts468_checked, qCounts468_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
