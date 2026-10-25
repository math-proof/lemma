/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk141.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk141.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts283_checked :
    rawMomentVCounts 283 = generatedVCounts283 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts283_checked :
    rawMomentQCounts 283 = generatedQCounts283 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients283_checked :
    rawMomentStateCoefficientList 283 = generatedStateCoefficients283 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts283_checked, qCounts283_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
