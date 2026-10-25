/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk064.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk064.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts129_checked :
    rawMomentVCounts 129 = generatedVCounts129 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts129_checked :
    rawMomentQCounts 129 = generatedQCounts129 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients129_checked :
    rawMomentStateCoefficientList 129 = generatedStateCoefficients129 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts129_checked, qCounts129_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
