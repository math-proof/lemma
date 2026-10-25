/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk020.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk020.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts41_checked :
    rawMomentVCounts 41 = generatedVCounts41 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts41_checked :
    rawMomentQCounts 41 = generatedQCounts41 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients41_checked :
    rawMomentStateCoefficientList 41 = generatedStateCoefficients41 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts41_checked, qCounts41_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
