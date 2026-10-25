/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk132.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk132.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts265_checked :
    rawMomentVCounts 265 = generatedVCounts265 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts265_checked :
    rawMomentQCounts 265 = generatedQCounts265 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients265_checked :
    rawMomentStateCoefficientList 265 = generatedStateCoefficients265 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts265_checked, qCounts265_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
