/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk026.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk026.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts53_checked :
    rawMomentVCounts 53 = generatedVCounts53 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts53_checked :
    rawMomentQCounts 53 = generatedQCounts53 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients53_checked :
    rawMomentStateCoefficientList 53 = generatedStateCoefficients53 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts53_checked, qCounts53_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
