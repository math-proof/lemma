/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk217.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk217.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts435_checked :
    rawMomentVCounts 435 = generatedVCounts435 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts435_checked :
    rawMomentQCounts 435 = generatedQCounts435 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients435_checked :
    rawMomentStateCoefficientList 435 = generatedStateCoefficients435 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts435_checked, qCounts435_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
