/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk161.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk161.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts323_checked :
    rawMomentVCounts 323 = generatedVCounts323 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts323_checked :
    rawMomentQCounts 323 = generatedQCounts323 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients323_checked :
    rawMomentStateCoefficientList 323 = generatedStateCoefficients323 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts323_checked, qCounts323_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
