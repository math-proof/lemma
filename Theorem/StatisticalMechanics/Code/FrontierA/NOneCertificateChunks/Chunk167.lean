/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk167.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk167


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts334_checked :
    rawMomentVCounts 334 = generatedVCounts334 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts334_checked :
    rawMomentQCounts 334 = generatedQCounts334 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients334_checked :
    rawMomentStateCoefficientList 334 = generatedStateCoefficients334 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts334_checked, qCounts334_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
