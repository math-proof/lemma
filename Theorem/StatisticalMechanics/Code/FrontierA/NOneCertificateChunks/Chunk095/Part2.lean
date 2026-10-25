/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk095.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk095.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts191_checked :
    rawMomentVCounts 191 = generatedVCounts191 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts191_checked :
    rawMomentQCounts 191 = generatedQCounts191 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients191_checked :
    rawMomentStateCoefficientList 191 = generatedStateCoefficients191 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts191_checked, qCounts191_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
