/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk120.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk120.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts241_checked :
    rawMomentVCounts 241 = generatedVCounts241 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts241_checked :
    rawMomentQCounts 241 = generatedQCounts241 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients241_checked :
    rawMomentStateCoefficientList 241 = generatedStateCoefficients241 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts241_checked, qCounts241_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
