/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk076.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk076.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts153_checked :
    rawMomentVCounts 153 = generatedVCounts153 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts153_checked :
    rawMomentQCounts 153 = generatedQCounts153 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients153_checked :
    rawMomentStateCoefficientList 153 = generatedStateCoefficients153 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts153_checked, qCounts153_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
