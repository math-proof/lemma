/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk183.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk183


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts366_checked :
    rawMomentVCounts 366 = generatedVCounts366 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts366_checked :
    rawMomentQCounts 366 = generatedQCounts366 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients366_checked :
    rawMomentStateCoefficientList 366 = generatedStateCoefficients366 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts366_checked, qCounts366_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
