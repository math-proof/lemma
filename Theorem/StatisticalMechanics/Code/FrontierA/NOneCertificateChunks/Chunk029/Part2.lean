/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk029.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk029.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts59_checked :
    rawMomentVCounts 59 = generatedVCounts59 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts59_checked :
    rawMomentQCounts 59 = generatedQCounts59 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients59_checked :
    rawMomentStateCoefficientList 59 = generatedStateCoefficients59 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts59_checked, qCounts59_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
