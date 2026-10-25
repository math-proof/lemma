/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk237.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk237.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts475_checked :
    rawMomentVCounts 475 = generatedVCounts475 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts475_checked :
    rawMomentQCounts 475 = generatedQCounts475 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients475_checked :
    rawMomentStateCoefficientList 475 = generatedStateCoefficients475 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts475_checked, qCounts475_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
