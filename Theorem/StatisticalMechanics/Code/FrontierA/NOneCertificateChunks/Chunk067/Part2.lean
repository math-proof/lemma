/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk067.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk067.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts135_checked :
    rawMomentVCounts 135 = generatedVCounts135 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts135_checked :
    rawMomentQCounts 135 = generatedQCounts135 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients135_checked :
    rawMomentStateCoefficientList 135 = generatedStateCoefficients135 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts135_checked, qCounts135_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
