/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk046.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk046


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts92_checked :
    rawMomentVCounts 92 = generatedVCounts92 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts92_checked :
    rawMomentQCounts 92 = generatedQCounts92 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients92_checked :
    rawMomentStateCoefficientList 92 = generatedStateCoefficients92 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts92_checked, qCounts92_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
