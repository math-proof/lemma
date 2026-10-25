/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk240.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk240


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts480_checked :
    rawMomentVCounts 480 = generatedVCounts480 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts480_checked :
    rawMomentQCounts 480 = generatedQCounts480 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients480_checked :
    rawMomentStateCoefficientList 480 = generatedStateCoefficients480 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts480_checked, qCounts480_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
