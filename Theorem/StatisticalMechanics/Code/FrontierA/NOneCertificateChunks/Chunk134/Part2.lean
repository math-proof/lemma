/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk134.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk134.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts269_checked :
    rawMomentVCounts 269 = generatedVCounts269 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts269_checked :
    rawMomentQCounts 269 = generatedQCounts269 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients269_checked :
    rawMomentStateCoefficientList 269 = generatedStateCoefficients269 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts269_checked, qCounts269_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
