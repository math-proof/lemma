/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk188.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk188.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts377_checked :
    rawMomentVCounts 377 = generatedVCounts377 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts377_checked :
    rawMomentQCounts 377 = generatedQCounts377 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients377_checked :
    rawMomentStateCoefficientList 377 = generatedStateCoefficients377 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts377_checked, qCounts377_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
