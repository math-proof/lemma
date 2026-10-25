/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk241.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk241.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts483_checked :
    rawMomentVCounts 483 = generatedVCounts483 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts483_checked :
    rawMomentQCounts 483 = generatedQCounts483 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients483_checked :
    rawMomentStateCoefficientList 483 = generatedStateCoefficients483 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts483_checked, qCounts483_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
