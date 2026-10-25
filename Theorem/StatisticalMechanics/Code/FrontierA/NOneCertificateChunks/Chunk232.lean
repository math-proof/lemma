/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk232.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk232


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts464_checked :
    rawMomentVCounts 464 = generatedVCounts464 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts464_checked :
    rawMomentQCounts 464 = generatedQCounts464 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients464_checked :
    rawMomentStateCoefficientList 464 = generatedStateCoefficients464 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts464_checked, qCounts464_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
