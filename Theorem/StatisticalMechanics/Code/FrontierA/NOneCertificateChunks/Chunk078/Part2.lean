/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk078.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk078.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts157_checked :
    rawMomentVCounts 157 = generatedVCounts157 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts157_checked :
    rawMomentQCounts 157 = generatedQCounts157 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients157_checked :
    rawMomentStateCoefficientList 157 = generatedStateCoefficients157 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts157_checked, qCounts157_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
