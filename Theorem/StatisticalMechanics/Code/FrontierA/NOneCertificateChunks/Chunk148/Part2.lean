/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk148.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk148.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts297_checked :
    rawMomentVCounts 297 = generatedVCounts297 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts297_checked :
    rawMomentQCounts 297 = generatedQCounts297 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients297_checked :
    rawMomentStateCoefficientList 297 = generatedStateCoefficients297 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts297_checked, qCounts297_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
