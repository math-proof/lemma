/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk077.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk077.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts155_checked :
    rawMomentVCounts 155 = generatedVCounts155 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts155_checked :
    rawMomentQCounts 155 = generatedQCounts155 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients155_checked :
    rawMomentStateCoefficientList 155 = generatedStateCoefficients155 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts155_checked, qCounts155_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
