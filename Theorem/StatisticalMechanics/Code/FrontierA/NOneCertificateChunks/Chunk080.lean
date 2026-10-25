/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk080.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk080


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts160_checked :
    rawMomentVCounts 160 = generatedVCounts160 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts160_checked :
    rawMomentQCounts 160 = generatedQCounts160 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients160_checked :
    rawMomentStateCoefficientList 160 = generatedStateCoefficients160 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts160_checked, qCounts160_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
