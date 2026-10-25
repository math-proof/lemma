/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk210.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk210.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts421_checked :
    rawMomentVCounts 421 = generatedVCounts421 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts421_checked :
    rawMomentQCounts 421 = generatedQCounts421 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients421_checked :
    rawMomentStateCoefficientList 421 = generatedStateCoefficients421 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts421_checked, qCounts421_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
