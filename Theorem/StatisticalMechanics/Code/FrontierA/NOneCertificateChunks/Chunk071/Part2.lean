/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk071.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk071.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts143_checked :
    rawMomentVCounts 143 = generatedVCounts143 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts143_checked :
    rawMomentQCounts 143 = generatedQCounts143 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients143_checked :
    rawMomentStateCoefficientList 143 = generatedStateCoefficients143 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts143_checked, qCounts143_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
