/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk040.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk040.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts81_checked :
    rawMomentVCounts 81 = generatedVCounts81 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts81_checked :
    rawMomentQCounts 81 = generatedQCounts81 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients81_checked :
    rawMomentStateCoefficientList 81 = generatedStateCoefficients81 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts81_checked, qCounts81_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
