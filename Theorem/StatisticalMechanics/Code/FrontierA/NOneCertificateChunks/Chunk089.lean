/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk089.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk089


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts178_checked :
    rawMomentVCounts 178 = generatedVCounts178 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts178_checked :
    rawMomentQCounts 178 = generatedQCounts178 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients178_checked :
    rawMomentStateCoefficientList 178 = generatedStateCoefficients178 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts178_checked, qCounts178_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
