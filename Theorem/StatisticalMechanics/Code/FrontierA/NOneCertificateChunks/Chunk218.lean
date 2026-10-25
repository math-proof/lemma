/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk218.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk218


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts436_checked :
    rawMomentVCounts 436 = generatedVCounts436 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts436_checked :
    rawMomentQCounts 436 = generatedQCounts436 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients436_checked :
    rawMomentStateCoefficientList 436 = generatedStateCoefficients436 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts436_checked, qCounts436_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
