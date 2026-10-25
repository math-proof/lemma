/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk248.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk248


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts496_checked :
    rawMomentVCounts 496 = generatedVCounts496 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts496_checked :
    rawMomentQCounts 496 = generatedQCounts496 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients496_checked :
    rawMomentStateCoefficientList 496 = generatedStateCoefficients496 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts496_checked, qCounts496_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
