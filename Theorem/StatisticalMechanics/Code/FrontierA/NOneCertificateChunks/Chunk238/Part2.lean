/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk238.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk238.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts477_checked :
    rawMomentVCounts 477 = generatedVCounts477 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts477_checked :
    rawMomentQCounts 477 = generatedQCounts477 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients477_checked :
    rawMomentStateCoefficientList 477 = generatedStateCoefficients477 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts477_checked, qCounts477_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
