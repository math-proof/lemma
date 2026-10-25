/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk128.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk128


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts256_checked :
    rawMomentVCounts 256 = generatedVCounts256 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts256_checked :
    rawMomentQCounts 256 = generatedQCounts256 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients256_checked :
    rawMomentStateCoefficientList 256 = generatedStateCoefficients256 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts256_checked, qCounts256_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
