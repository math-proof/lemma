/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk097.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk097


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts194_checked :
    rawMomentVCounts 194 = generatedVCounts194 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts194_checked :
    rawMomentQCounts 194 = generatedQCounts194 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients194_checked :
    rawMomentStateCoefficientList 194 = generatedStateCoefficients194 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts194_checked, qCounts194_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
