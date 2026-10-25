/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk198.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk198.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts397_checked :
    rawMomentVCounts 397 = generatedVCounts397 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts397_checked :
    rawMomentQCounts 397 = generatedQCounts397 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients397_checked :
    rawMomentStateCoefficientList 397 = generatedStateCoefficients397 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts397_checked, qCounts397_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
