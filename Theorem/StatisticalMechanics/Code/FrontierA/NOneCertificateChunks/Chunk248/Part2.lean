/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk248.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk248.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts497_checked :
    rawMomentVCounts 497 = generatedVCounts497 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts497_checked :
    rawMomentQCounts 497 = generatedQCounts497 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients497_checked :
    rawMomentStateCoefficientList 497 = generatedStateCoefficients497 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts497_checked, qCounts497_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
