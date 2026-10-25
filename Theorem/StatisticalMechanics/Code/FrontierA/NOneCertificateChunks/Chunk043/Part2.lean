/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk043.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk043.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts87_checked :
    rawMomentVCounts 87 = generatedVCounts87 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts87_checked :
    rawMomentQCounts 87 = generatedQCounts87 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients87_checked :
    rawMomentStateCoefficientList 87 = generatedStateCoefficients87 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts87_checked, qCounts87_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
