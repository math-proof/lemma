/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk043.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk043


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts86_checked :
    rawMomentVCounts 86 = generatedVCounts86 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts86_checked :
    rawMomentQCounts 86 = generatedQCounts86 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients86_checked :
    rawMomentStateCoefficientList 86 = generatedStateCoefficients86 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts86_checked, qCounts86_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
