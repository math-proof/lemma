/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk252.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk252.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts505_checked :
    rawMomentVCounts 505 = generatedVCounts505 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts505_checked :
    rawMomentQCounts 505 = generatedQCounts505 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients505_checked :
    rawMomentStateCoefficientList 505 = generatedStateCoefficients505 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts505_checked, qCounts505_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
