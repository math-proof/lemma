/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk130.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk130.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts261_checked :
    rawMomentVCounts 261 = generatedVCounts261 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts261_checked :
    rawMomentQCounts 261 = generatedQCounts261 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients261_checked :
    rawMomentStateCoefficientList 261 = generatedStateCoefficients261 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts261_checked, qCounts261_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
