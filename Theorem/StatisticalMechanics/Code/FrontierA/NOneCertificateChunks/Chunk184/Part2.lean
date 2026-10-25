/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk184.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk184.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts369_checked :
    rawMomentVCounts 369 = generatedVCounts369 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts369_checked :
    rawMomentQCounts 369 = generatedQCounts369 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients369_checked :
    rawMomentStateCoefficientList 369 = generatedStateCoefficients369 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts369_checked, qCounts369_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
