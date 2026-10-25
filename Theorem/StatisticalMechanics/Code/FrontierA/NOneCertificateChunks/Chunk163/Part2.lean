/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk163.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk163.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts327_checked :
    rawMomentVCounts 327 = generatedVCounts327 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts327_checked :
    rawMomentQCounts 327 = generatedQCounts327 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients327_checked :
    rawMomentStateCoefficientList 327 = generatedStateCoefficients327 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts327_checked, qCounts327_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
