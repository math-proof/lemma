/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk219.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk219.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts439_checked :
    rawMomentVCounts 439 = generatedVCounts439 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts439_checked :
    rawMomentQCounts 439 = generatedQCounts439 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients439_checked :
    rawMomentStateCoefficientList 439 = generatedStateCoefficients439 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts439_checked, qCounts439_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
