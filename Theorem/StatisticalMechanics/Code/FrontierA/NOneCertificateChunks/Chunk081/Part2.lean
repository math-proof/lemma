/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk081.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk081.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts163_checked :
    rawMomentVCounts 163 = generatedVCounts163 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts163_checked :
    rawMomentQCounts 163 = generatedQCounts163 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients163_checked :
    rawMomentStateCoefficientList 163 = generatedStateCoefficients163 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts163_checked, qCounts163_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
