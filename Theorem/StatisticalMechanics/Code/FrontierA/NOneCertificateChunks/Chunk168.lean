/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk168.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk168


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts336_checked :
    rawMomentVCounts 336 = generatedVCounts336 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts336_checked :
    rawMomentQCounts 336 = generatedQCounts336 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients336_checked :
    rawMomentStateCoefficientList 336 = generatedStateCoefficients336 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts336_checked, qCounts336_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
