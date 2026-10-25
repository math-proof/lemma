/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk172.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk172.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts345_checked :
    rawMomentVCounts 345 = generatedVCounts345 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts345_checked :
    rawMomentQCounts 345 = generatedQCounts345 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients345_checked :
    rawMomentStateCoefficientList 345 = generatedStateCoefficients345 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts345_checked, qCounts345_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
