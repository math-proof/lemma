/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk198.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk198


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts396_checked :
    rawMomentVCounts 396 = generatedVCounts396 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts396_checked :
    rawMomentQCounts 396 = generatedQCounts396 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients396_checked :
    rawMomentStateCoefficientList 396 = generatedStateCoefficients396 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts396_checked, qCounts396_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
