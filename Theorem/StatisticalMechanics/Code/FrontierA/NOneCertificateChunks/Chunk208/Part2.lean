/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk208.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk208.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts417_checked :
    rawMomentVCounts 417 = generatedVCounts417 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts417_checked :
    rawMomentQCounts 417 = generatedQCounts417 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients417_checked :
    rawMomentStateCoefficientList 417 = generatedStateCoefficients417 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts417_checked, qCounts417_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
