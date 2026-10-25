/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk177.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk177.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts355_checked :
    rawMomentVCounts 355 = generatedVCounts355 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts355_checked :
    rawMomentQCounts 355 = generatedQCounts355 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients355_checked :
    rawMomentStateCoefficientList 355 = generatedStateCoefficients355 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts355_checked, qCounts355_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
