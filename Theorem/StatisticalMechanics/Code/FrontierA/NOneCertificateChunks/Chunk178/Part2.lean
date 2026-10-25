/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk178.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk178.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts357_checked :
    rawMomentVCounts 357 = generatedVCounts357 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts357_checked :
    rawMomentQCounts 357 = generatedQCounts357 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients357_checked :
    rawMomentStateCoefficientList 357 = generatedStateCoefficients357 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts357_checked, qCounts357_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
