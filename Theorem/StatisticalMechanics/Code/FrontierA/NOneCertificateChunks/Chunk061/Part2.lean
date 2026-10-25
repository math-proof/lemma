/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk061.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk061.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts123_checked :
    rawMomentVCounts 123 = generatedVCounts123 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts123_checked :
    rawMomentQCounts 123 = generatedQCounts123 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients123_checked :
    rawMomentStateCoefficientList 123 = generatedStateCoefficients123 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts123_checked, qCounts123_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
