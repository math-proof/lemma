/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk091.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk091.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts183_checked :
    rawMomentVCounts 183 = generatedVCounts183 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts183_checked :
    rawMomentQCounts 183 = generatedQCounts183 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients183_checked :
    rawMomentStateCoefficientList 183 = generatedStateCoefficients183 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts183_checked, qCounts183_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
