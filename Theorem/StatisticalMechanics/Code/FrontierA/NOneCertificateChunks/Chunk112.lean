/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk112.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk112


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts224_checked :
    rawMomentVCounts 224 = generatedVCounts224 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts224_checked :
    rawMomentQCounts 224 = generatedQCounts224 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients224_checked :
    rawMomentStateCoefficientList 224 = generatedStateCoefficients224 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts224_checked, qCounts224_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
