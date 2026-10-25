/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk202.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk202.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts405_checked :
    rawMomentVCounts 405 = generatedVCounts405 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts405_checked :
    rawMomentQCounts 405 = generatedQCounts405 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients405_checked :
    rawMomentStateCoefficientList 405 = generatedStateCoefficients405 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts405_checked, qCounts405_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
