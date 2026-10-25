/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk165.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk165.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts331_checked :
    rawMomentVCounts 331 = generatedVCounts331 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts331_checked :
    rawMomentQCounts 331 = generatedQCounts331 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients331_checked :
    rawMomentStateCoefficientList 331 = generatedStateCoefficients331 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts331_checked, qCounts331_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
