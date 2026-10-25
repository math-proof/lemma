/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk247.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk247.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts495_checked :
    rawMomentVCounts 495 = generatedVCounts495 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts495_checked :
    rawMomentQCounts 495 = generatedQCounts495 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients495_checked :
    rawMomentStateCoefficientList 495 = generatedStateCoefficients495 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts495_checked, qCounts495_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
