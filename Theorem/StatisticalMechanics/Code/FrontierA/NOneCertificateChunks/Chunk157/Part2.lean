/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk157.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk157.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts315_checked :
    rawMomentVCounts 315 = generatedVCounts315 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts315_checked :
    rawMomentQCounts 315 = generatedQCounts315 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients315_checked :
    rawMomentStateCoefficientList 315 = generatedStateCoefficients315 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts315_checked, qCounts315_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
