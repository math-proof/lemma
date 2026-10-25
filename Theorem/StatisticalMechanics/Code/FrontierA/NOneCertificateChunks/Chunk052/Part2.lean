/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk052.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk052.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts105_checked :
    rawMomentVCounts 105 = generatedVCounts105 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts105_checked :
    rawMomentQCounts 105 = generatedQCounts105 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients105_checked :
    rawMomentStateCoefficientList 105 = generatedStateCoefficients105 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts105_checked, qCounts105_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
