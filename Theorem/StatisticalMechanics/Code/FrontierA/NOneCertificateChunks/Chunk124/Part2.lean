/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk124.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk124.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts249_checked :
    rawMomentVCounts 249 = generatedVCounts249 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts249_checked :
    rawMomentQCounts 249 = generatedQCounts249 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients249_checked :
    rawMomentStateCoefficientList 249 = generatedStateCoefficients249 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts249_checked, qCounts249_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
