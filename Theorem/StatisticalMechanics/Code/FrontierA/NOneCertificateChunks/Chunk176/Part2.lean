/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk176.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk176.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts353_checked :
    rawMomentVCounts 353 = generatedVCounts353 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts353_checked :
    rawMomentQCounts 353 = generatedQCounts353 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients353_checked :
    rawMomentStateCoefficientList 353 = generatedStateCoefficients353 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts353_checked, qCounts353_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
