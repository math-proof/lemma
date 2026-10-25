/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk224.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk224.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts449_checked :
    rawMomentVCounts 449 = generatedVCounts449 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts449_checked :
    rawMomentQCounts 449 = generatedQCounts449 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients449_checked :
    rawMomentStateCoefficientList 449 = generatedStateCoefficients449 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts449_checked, qCounts449_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
