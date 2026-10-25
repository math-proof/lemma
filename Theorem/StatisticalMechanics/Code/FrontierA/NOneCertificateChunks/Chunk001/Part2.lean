/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk001.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk001.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts3_checked :
    rawMomentVCounts 3 = generatedVCounts3 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts3_checked :
    rawMomentQCounts 3 = generatedQCounts3 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients3_checked :
    rawMomentStateCoefficientList 3 = generatedStateCoefficients3 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts3_checked, qCounts3_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
