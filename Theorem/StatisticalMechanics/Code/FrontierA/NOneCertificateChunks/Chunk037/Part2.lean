/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk037.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk037.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts75_checked :
    rawMomentVCounts 75 = generatedVCounts75 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts75_checked :
    rawMomentQCounts 75 = generatedQCounts75 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients75_checked :
    rawMomentStateCoefficientList 75 = generatedStateCoefficients75 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts75_checked, qCounts75_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
